module

public import BlackHole.RK4Consistency
public import BlackHole.KerrCompact
public import BlackHole.RayGrowth
public import BlackHole.AdaptiveStep
import Mathlib.Tactic.GCongr

/-! RK4 perturbation growth and accumulated error (N2).
All four stages of both compared steps must lie in the Lipschitz region.
Local truncation and roundoff enter as separate, explicit budgets. -/

@[expose] public section
noncomputable section

open Set
open scoped NNReal

namespace BlackHole.RK4Consistency

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every field evaluation made by a classical RK4 step lies in `s`. -/
def StagesIn (f : E → E) (s : Set E) (y : E) (h : ℝ) : Prop :=
  y ∈ s ∧ y+(h/2) • f y ∈ s ∧
    y+(h/2) • k2 f y h ∈ s ∧ y+h • k3 f y h ∈ s

private lemma offset_bound (y z u v : E) (c : ℝ) :
    ‖(y+c • u)-(z+c • v)‖ ≤ ‖y-z‖+|c| * ‖u-v‖ := by
  calc _ = ‖(y-z)+c • (u-v)‖ := by congr 1; module
    _ ≤ ‖y-z‖+‖c • (u-v)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs]

/-- A bound on the field and clearance of a whole ball suffice to keep every
stage in the region; checking only the step endpoint is insufficient. -/
theorem stagesIn_of_ball (f : E → E) {s : Set E} (y : E) (h M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hball : Metric.closedBall y (|h| * M) ⊆ s) : StagesIn f s y h := by
  have hmem (c : ℝ) (u : E) (hc : |c| ≤ |h|) (hu : ‖u‖ ≤ M) : y+c • u ∈ s := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hu (norm_nonneg _) (abs_nonneg _)
  have hy : y ∈ s := hball (Metric.mem_closedBall_self (by positivity))
  have hhalf : |h/2| ≤ |h| := by rw [abs_div]; norm_num
  have h2 := hmem (h/2) (f y) hhalf (hbound y hy)
  have h3 := hmem (h/2) (k2 f y h) hhalf (hbound _ h2)
  exact ⟨hy, h2, h3, hmem h (k3 f y h) le_rfl (hbound _ h3)⟩

/-- The nonlinear RK4 step amplifies perturbations by at most the classical
stability polynomial at `K |h|`, provided both sets of stages stay in `s`. -/
theorem rk4_step_stability (f : E → E) {s : Set E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (y z : E) (h : ℝ)
    (hy : StagesIn f s y h) (hz : StagesIn f s z h) :
    ‖rk4Step f y h-rk4Step f z h‖ ≤
      Numerics.rk4Polynomial (K*|h|)*‖y-z‖ := by
  let e := ‖y-z‖
  let b1 := (K : ℝ)*e
  let b2 := (K : ℝ)*(e+(|h|/2)*b1)
  let b3 := (K : ℝ)*(e+(|h|/2)*b2)
  let b4 := (K : ℝ)*(e+|h| * b3)
  have hhalf : |h/2| = |h|/2 := by rw [abs_div]; norm_num
  have h1 : ‖f y-f z‖ ≤ b1 := hlip.norm_sub_le hy.1 hz.1
  have h2 : ‖k2 f y h-k2 f z h‖ ≤ b2 := by
    calc _ ≤ K*‖(y+(h/2) • f y)-(z+(h/2) • f z)‖ :=
          hlip.norm_sub_le hy.2.1 hz.2.1
      _ ≤ K*(e+(|h|/2)*b1) := by
        apply mul_le_mul_of_nonneg_left _ K.2
        exact (offset_bound y z (f y) (f z) (h/2)).trans (by rw [hhalf]; gcongr)
  have h3 : ‖k3 f y h-k3 f z h‖ ≤ b3 := by
    calc _ ≤ K*‖(y+(h/2) • k2 f y h)-(z+(h/2) • k2 f z h)‖ :=
          hlip.norm_sub_le hy.2.2.1 hz.2.2.1
      _ ≤ K*(e+(|h|/2)*b2) := by
        apply mul_le_mul_of_nonneg_left _ K.2
        exact (offset_bound y z (k2 f y h) (k2 f z h) (h/2)).trans
          (by rw [hhalf]; gcongr)
  have h4 : ‖k4 f y h-k4 f z h‖ ≤ b4 := by
    calc _ ≤ K*‖(y+h • k3 f y h)-(z+h • k3 f z h)‖ :=
          hlip.norm_sub_le hy.2.2.2 hz.2.2.2
      _ ≤ K*(e+|h| * b3) := by
        apply mul_le_mul_of_nonneg_left _ K.2
        exact (offset_bound y z (k3 f y h) (k3 f z h) h).trans (by gcongr)
  have hw : ‖(f y+(2:ℝ) • k2 f y h+(2:ℝ) • k3 f y h+k4 f y h)-
      (f z+(2:ℝ) • k2 f z h+(2:ℝ) • k3 f z h+k4 f z h)‖ ≤
      b1+2*b2+2*b3+b4 := by
    calc _ = ‖(f y-f z)+(2:ℝ) • (k2 f y h-k2 f z h)+
          (2:ℝ) • (k3 f y h-k3 f z h)+(k4 f y h-k4 f z h)‖ := by
            congr 1; module
      _ ≤ ‖f y-f z‖+‖(2:ℝ) • (k2 f y h-k2 f z h)‖+
          ‖(2:ℝ) • (k3 f y h-k3 f z h)‖+‖k4 f y h-k4 f z h‖ := by
            exact (norm_add_le _ _).trans (add_le_add
              ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]; gcongr
  calc _ ≤ e+|h/6| * ‖(f y+(2:ℝ) • k2 f y h+(2:ℝ) • k3 f y h+k4 f y h)-
        (f z+(2:ℝ) • k2 f z h+(2:ℝ) • k3 f z h+k4 f z h)‖ :=
          offset_bound _ _ _ _ _
    _ ≤ e+(|h|/6)*(b1+2*b2+2*b3+b4) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<6)]
      gcongr
    _ = Numerics.rk4Polynomial (K*|h|)*‖y-z‖ := by
      dsimp [e, b1, b2, b3, b4, Numerics.rk4Polynomial]
      ring

/-- The RK4 perturbation factor is bounded by the usual exponential growth. -/
theorem rk4Polynomial_le_exp (z : ℝ) (hz : 0 ≤ z) :
    Numerics.rk4Polynomial z ≤ Real.exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 5
  simpa [Numerics.rk4Polynomial, Finset.sum_range_succ, Nat.factorial,
    add_assoc] using h

/-- Uniform one-step perturbation growth for the actual Kerr field on a
bounded exterior region. The Lipschitz constant is derived from the source. -/
theorem kerr_rk4_step_stability (mass : ℝ) (a : Cartesian.Space) (ρ R P F : ℝ)
    (hρ : 0 < ρ) :
    ∃ K : ℝ≥0, ∀ y z : KerrField.Phase, ∀ h : ℝ,
      StagesIn (KerrField.phaseRhs mass a) (KerrField.phaseRegion a ρ R P F) y h →
      StagesIn (KerrField.phaseRhs mass a) (KerrField.phaseRegion a ρ R P F) z h →
      ‖rk4Step (KerrField.phaseRhs mass a) y h-rk4Step (KerrField.phaseRhs mass a) z h‖ ≤
        Numerics.rk4Polynomial (K*|h|)*‖y-z‖ := by
  obtain ⟨K, hK⟩ := (KerrField.phaseRegion_bounds mass a ρ R P F hρ).2
  exact ⟨K, fun y z h hy hz => rk4_step_stability _ hK y z h hy hz⟩

/-- A computed step may include roundoff or other implementation error. Its
distance from the next exact state includes propagation and local defect. -/
theorem rk4_error_recurrence (f : E → E) {s : Set E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (y z computed exact : E) (h trunc roundoff : ℝ)
    (hy : StagesIn f s y h) (hz : StagesIn f s z h)
    (hround : ‖computed-rk4Step f y h‖ ≤ roundoff)
    (htrunc : ‖rk4Step f z h-exact‖ ≤ trunc) :
    ‖computed-exact‖ ≤ Numerics.rk4Polynomial (K*|h|)*‖y-z‖+trunc+roundoff := by
  calc _ ≤ ‖computed-rk4Step f y h‖+‖rk4Step f y h-rk4Step f z h‖+
        ‖rk4Step f z h-exact‖ := by
          exact (norm_sub_le_norm_sub_add_norm_sub computed (rk4Step f z h) exact).trans
            (add_le_add
              (norm_sub_le_norm_sub_add_norm_sub computed (rk4Step f y h) (rk4Step f z h)) le_rfl)
    _ ≤ roundoff+Numerics.rk4Polynomial (K*|h|)*‖y-z‖+trunc :=
      add_le_add (add_le_add hround (rk4_step_stability f hlip y z h hy hz)) htrunc
    _ = _ := by ring

/-- Variable steps and nonzero initial error: the actual RK4 propagation bound
supplies the growth term in the existing accumulated-error budget theorem. -/
theorem rk4_variable_error_budget (f : E → E) {s : Set E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (approx exact : ℕ → E)
    (step trunc roundoff budget : ℕ → ℝ)
    (ha : ∀ n, StagesIn f s (approx n) (step n))
    (he : ∀ n, StagesIn f s (exact n) (step n))
    (hzero : ‖approx 0-exact 0‖ ≤ budget 0)
    (hround : ∀ n, ‖approx (n+1)-rk4Step f (approx n) (step n)‖ ≤ roundoff n)
    (htrunc : ∀ n, ‖rk4Step f (exact n) (step n)-exact (n+1)‖ ≤ trunc n)
    (hbudget : ∀ n, Numerics.rk4Polynomial (K*|step n|)*budget n+
      trunc n+roundoff n ≤ budget (n+1)) :
    ∀ n, ‖approx n-exact n‖ ≤ budget n := by
  apply AdaptiveStep.variable_error_budget (fun n => ‖approx n-exact n‖)
    (fun n => Numerics.rk4Polynomial (K*|step n|))
    (fun n => trunc n+roundoff n) budget hzero
  · intro n
    unfold Numerics.rk4Polynomial
    positivity
  · intro n
    simpa only [add_assoc] using rk4_error_recurrence f hlip (approx n) (exact n)
      (approx (n+1)) (exact (n+1)) (step n) (trunc n) (roundoff n)
      (ha n) (he n) (hround n) (htrunc n)
  · intro n
    simpa only [add_assoc] using hbudget n

private lemma rk4_exp_budget (K : ℝ≥0) (h initial d : ℝ)
    (hh : 0 ≤ h) (hinitial : 0 ≤ initial) (hd : 0 ≤ d) (n : ℕ) :
    Numerics.rk4Polynomial (K*h)*((initial+(n:ℝ)*d)*Real.exp (K*((n:ℝ)*h)))+d ≤
      (initial+((n+1:ℕ):ℝ)*d)*Real.exp (K*(((n+1:ℕ):ℝ)*h)) := by
  have hpoly := rk4Polynomial_le_exp (K*h) (by positivity)
  have hexp : 1 ≤ Real.exp (K*(((n+1:ℕ):ℝ)*h)) := Real.one_le_exp (by positivity)
  have heq : Real.exp (K*h)*Real.exp (K*((n:ℝ)*h)) =
      Real.exp (K*(((n+1:ℕ):ℝ)*h)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc _ ≤ Real.exp (K*h)*((initial+(n:ℝ)*d)*Real.exp (K*((n:ℝ)*h)))+
        d*Real.exp (K*(((n+1:ℕ):ℝ)*h)) :=
          add_le_add (mul_le_mul_of_nonneg_right hpoly (by positivity))
            (le_mul_of_one_le_right hd hexp)
    _ = _ := by
      rw [mul_left_comm (Real.exp (K*h)), heq]
      push_cast
      ring

/-- A fixed-step global bound with initial error and a per-step roundoff term.
For zero roundoff and initial error it is `C T exp(K T) h⁴` at time `T = n h`.
The uniform local defect and stage containment are explicit hypotheses. -/
theorem rk4_fixed_error_bound (f : E → E) {s : Set E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (approx exact : ℕ → E) (h C roundoff initial : ℝ)
    (hh : 0 ≤ h) (hC : 0 ≤ C) (hroundoff : 0 ≤ roundoff) (hinitial : 0 ≤ initial)
    (ha : ∀ n, StagesIn f s (approx n) h) (he : ∀ n, StagesIn f s (exact n) h)
    (hzero : ‖approx 0-exact 0‖ ≤ initial)
    (hround : ∀ n, ‖approx (n+1)-rk4Step f (approx n) h‖ ≤ roundoff)
    (htrunc : ∀ n, ‖rk4Step f (exact n) h-exact (n+1)‖ ≤ C*h^5) :
    ∀ n, ‖approx n-exact n‖ ≤
      (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) := by
  let d := C*h^5+roundoff
  have hd : 0 ≤ d := by dsimp [d]; positivity
  apply rk4_variable_error_budget f hlip approx exact (fun _ => h)
    (fun _ => C*h^5) (fun _ => roundoff)
    (fun n => (initial+(n:ℝ)*d)*Real.exp (K*((n:ℝ)*h))) ha he
  · simpa using hzero
  · exact hround
  · exact htrunc
  · intro n
    rw [abs_of_nonneg hh]
    simpa only [d, add_assoc] using rk4_exp_budget K h initial d hh hinitial hd n

/-- The finite-horizon version needs certificates only for steps before `N`.
It does not assume the trajectory exists or stays in the region forever. -/
theorem rk4_fixed_error_bound_upto (f : E → E) {s : Set E} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (approx exact : ℕ → E) (N : ℕ)
    (h C roundoff initial : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hroundoff : 0 ≤ roundoff) (hinitial : 0 ≤ initial)
    (ha : ∀ n < N, StagesIn f s (approx n) h) (he : ∀ n < N, StagesIn f s (exact n) h)
    (hzero : ‖approx 0-exact 0‖ ≤ initial)
    (hround : ∀ n < N, ‖approx (n+1)-rk4Step f (approx n) h‖ ≤ roundoff)
    (htrunc : ∀ n < N, ‖rk4Step f (exact n) h-exact (n+1)‖ ≤ C*h^5) :
    ∀ n ≤ N, ‖approx n-exact n‖ ≤
      (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) := by
  let d := C*h^5+roundoff
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hg : 0 ≤ Numerics.rk4Polynomial (K*|h|) := by
    unfold Numerics.rk4Polynomial
    positivity
  intro n
  induction n with
  | zero => intro _; simpa using hzero
  | succ n ih =>
    intro hn
    have hnN : n < N := Nat.lt_of_succ_le hn
    have hb := ih (Nat.le_of_lt hnN)
    have hs := rk4_error_recurrence f hlip (approx n) (exact n) (approx (n+1)) (exact (n+1))
      h (C*h^5) roundoff (ha n hnN) (he n hnN) (hround n hnN) (htrunc n hnN)
    calc _ ≤ Numerics.rk4Polynomial (K*|h|)*‖approx n-exact n‖+C*h^5+roundoff := hs
      _ ≤ Numerics.rk4Polynomial (K*|h|)*
          ((initial+(n:ℝ)*d)*Real.exp (K*((n:ℝ)*h)))+d := by
            simpa only [d, add_assoc] using
              add_le_add (mul_le_mul_of_nonneg_left hb hg) (le_refl (C*h^5+roundoff))
      _ ≤ _ := by
        rw [abs_of_nonneg hh]
        exact rk4_exp_budget K h initial d hh hinitial hd n

end BlackHole.RK4Consistency
