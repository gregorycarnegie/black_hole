module

public import BlackHole.WgslExpr

/-! Reassociation of sums (obligation F2).

WGSL lets an implementation reassociate operations (§15.7.5): `(a + b) + c`
may be evaluated as `a + (b + c)`, and `(a - b) + c` as `(a + c) - b`. The
running bound of `WgslExpr` follows one association. Here a maximal chain of
`+`, `-` and negation is described by its signed leaves (`sumLeaves`), and
`RA e e'` says that `e'` evaluates the same sum chains as `e`, in any
association and order, with related leaves.

`RA` preserves the exact value (`exact_RA`), and every association of a
chain with `n` leaves `tᵢ` with bounds `Bᵢ` has running bound at most
`((1+U)ⁿ⁻¹ - 1) Σ|tᵢ| + (1+U)ⁿ⁻¹ Σ Bᵢ + (n-1)(1+U)ⁿ⁻¹ η` (`sum_bound`).
Products and quotients are kept in their source association. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslReassoc
open Wgsl WgslPoly WgslExpr GExpr

/-- Roots of sum chains. -/
def IsSum : GExpr → Prop
  | .add _ _ => True
  | .sub _ _ => True
  | .neg _ => True
  | _ => False

instance (e : GExpr) : Decidable (IsSum e) := by
  cases e <;> simp only [IsSum] <;> infer_instance

/-- The leaves of the maximal sum chain at `e`, `true` when negated. -/
def sumLeaves : GExpr → List (Bool × GExpr)
  | .add a b => sumLeaves a ++ sumLeaves b
  | .sub a b => sumLeaves a ++ (sumLeaves b).map fun p => (!p.1, p.2)
  | .neg a => (sumLeaves a).map fun p => (!p.1, p.2)
  | e => [(false, e)]

lemma sumLeaves_of_not {e : GExpr} (h : ¬ IsSum e) : sumLeaves e = [(false, e)] := by
  cases e <;> simp_all [IsSum, sumLeaves]

lemma sumLeaves_leaf : ∀ (e : GExpr), ∀ p ∈ sumLeaves e, ¬ IsSum p.2
  | .add a b => by
    intro p hp; simp only [sumLeaves, List.mem_append] at hp
    rcases hp with h | h
    · exact sumLeaves_leaf a p h
    · exact sumLeaves_leaf b p h
  | .sub a b => by
    intro p hp; simp only [sumLeaves, List.mem_append, List.mem_map] at hp
    rcases hp with h | ⟨q, hq, rfl⟩
    · exact sumLeaves_leaf a p h
    · exact sumLeaves_leaf b q hq
  | .neg a => by
    intro p hp; simp only [sumLeaves, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact sumLeaves_leaf a q hq
  | .input _ | .const _ | .mul _ _ | .div _ _ | .sqrt _ | .max _ _ | .min _ _ | .lt _ _ _ _
  | .abs _ | .invsqrt _ | .exp _ | .exp2 _ | .log _ | .log2 _ | .inh _ _ | .tanh _ _
  | .lt2 _ _ _ _ | .sinS _ | .cosS _ | .scale _ _ | .round _ | .qsel _ _ _ _ => by
    intro p hp; simp only [sumLeaves, List.mem_singleton] at hp; subst hp; simp [IsSum]

set_option linter.unusedSimpArgs false in
lemma sumLeaves_size : ∀ (e : GExpr), IsSum e → ∀ p ∈ sumLeaves e, sizeOf p.2 < sizeOf e
  | .add a b, _ => by
    intro p hp; simp only [sumLeaves, List.mem_append] at hp
    rcases hp with h | h
    · by_cases ha : IsSum a
      · have := sumLeaves_size a ha p h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
      · rw [sumLeaves_of_not ha] at h; simp at h; subst h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
    · by_cases hb : IsSum b
      · have := sumLeaves_size b hb p h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
      · rw [sumLeaves_of_not hb] at h; simp at h; subst h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
  | .sub a b, _ => by
    intro p hp; simp only [sumLeaves, List.mem_append, List.mem_map] at hp
    rcases hp with h | ⟨q, hq, rfl⟩
    · by_cases ha : IsSum a
      · have := sumLeaves_size a ha p h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
      · rw [sumLeaves_of_not ha] at h; simp at h; subst h; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
    · by_cases hb : IsSum b
      · have := sumLeaves_size b hb q hq; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
      · rw [sumLeaves_of_not hb] at hq; simp at hq; subst hq; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
  | .neg a, _ => by
    intro p hp; simp only [sumLeaves, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    by_cases ha : IsSum a
    · have := sumLeaves_size a ha q hq; simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.neg.sizeOf_spec]; omega
    · rw [sumLeaves_of_not ha] at hq; simp at hq; subst hq
      simp only [GExpr.neg.sizeOf_spec]; omega
  | .input _, h | .const _, h | .mul _ _, h | .div _ _, h | .sqrt _, h | .max _ _, h
  | .min _ _, h | .lt _ _ _ _, h | .abs _, h | .invsqrt _, h | .exp _, h | .exp2 _, h
  | .log _, h | .log2 _, h | .inh _ _, h | .tanh _ _, h | .lt2 _ _ _ _, h | .sinS _, h
  | .cosS _, h | .scale _ _, h | .round _, h | .qsel _ _ _ _, h => absurd h (by simp [IsSum])

lemma sum_map_neg {α : Type*} (L : List α) (f : α → ℝ) :
    (L.map fun x => -f x).sum = -(L.map f).sum := by
  induction L <;> simp [*]; ring

lemma abs_sum_map_le {α : Type*} (L : List α) (f : α → ℝ) :
    |(L.map f).sum| ≤ (L.map fun x => |f x|).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (by linarith)

/-- `±1` for a leaf sign. -/
def sgn (s : Bool) : ℝ := if s then -1 else 1

lemma sum_exact (v : ℕ → ℝ) : ∀ e : GExpr,
    e.exact v = ((sumLeaves e).map fun p => sgn p.1*p.2.exact v).sum
  | .add a b => by
    simp only [sumLeaves, exact, List.map_append, List.sum_append, sum_exact v a, sum_exact v b]
  | .sub a b => by
    simp only [sumLeaves, exact, List.map_append, List.sum_append, sum_exact v a, sum_exact v b,
      List.map_map]
    rw [sub_eq_add_neg, ← sum_map_neg]
    congr 2; apply List.map_congr_left; intro p _; obtain ⟨s, x⟩ := p; cases s <;> simp [sgn]
  | .neg a => by
    simp only [sumLeaves, exact, List.map_map, sum_exact v a]
    rw [← sum_map_neg]
    congr 1; apply List.map_congr_left; intro p _; obtain ⟨s, x⟩ := p; cases s <;> simp [sgn]
  | .input _ | .const _ | .mul _ _ | .div _ _ | .sqrt _ | .max _ _ | .min _ _ | .lt _ _ _ _
  | .abs _ | .invsqrt _ | .exp _ | .exp2 _ | .log _ | .log2 _ | .inh _ _ | .tanh _ _
  | .lt2 _ _ _ _ | .sinS _ | .cosS _ | .scale _ _ | .round _ | .qsel _ _ _ _ => by
    simp [sumLeaves, sgn]

/-- Leaf magnitudes and leaf bounds of a chain. -/
def lmag (v : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ := (L.map fun p => |p.2.exact v|).sum
def lbnd (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ := (L.map fun p => p.2.bound v E).sum

lemma abs_exact_le (v : ℕ → ℝ) (e : GExpr) : |e.exact v| ≤ lmag v (sumLeaves e) := by
  rw [sum_exact v e, lmag]
  refine (abs_sum_map_le _ _).trans (le_of_eq ?_)
  congr 1; apply List.map_congr_left; intro p _
  obtain ⟨s, x⟩ := p; cases s <;> simp [sgn]

lemma lmag_nonneg (v : ℕ → ℝ) (L : List (Bool × GExpr)) : 0 ≤ lmag v L :=
  List.sum_nonneg fun x hx => by obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _

lemma lbnd_nonneg {v E : ℕ → ℝ} {L : List (Bool × GExpr)} (h : ∀ p ∈ L, 0 ≤ p.2.bound v E) :
    0 ≤ lbnd v E L :=
  List.sum_nonneg fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact h p hp

lemma lmag_flip (v : ℕ → ℝ) (L : List (Bool × GExpr)) :
    lmag v (L.map fun p => (!p.1, p.2)) = lmag v L := by simp [lmag, List.map_map, Function.comp_def]

lemma lbnd_flip (v E : ℕ → ℝ) (L : List (Bool × GExpr)) :
    lbnd v E (L.map fun p => (!p.1, p.2)) = lbnd v E L := by
  simp [lbnd, List.map_map, Function.comp_def]

lemma sumLeaves_length_pos : ∀ e : GExpr, 0 < (sumLeaves e).length
  | .add a b => by simp [sumLeaves]; have := sumLeaves_length_pos a; omega
  | .sub a b => by simp [sumLeaves]; have := sumLeaves_length_pos a; omega
  | .neg a => by simp [sumLeaves]; exact sumLeaves_length_pos a
  | .input _ | .const _ | .mul _ _ | .div _ _ | .sqrt _ | .max _ _ | .min _ _ | .lt _ _ _ _
  | .abs _ | .invsqrt _ | .exp _ | .exp2 _ | .log _ | .log2 _ | .inh _ _ | .tanh _ _
  | .lt2 _ _ _ _ | .sinS _ | .cosS _ | .scale _ _ | .round _ | .qsel _ _ _ _ => by simp [sumLeaves]

/-- The `η` coefficient of a chain of `n` leaves. -/
lemma eta_step (U : ℝ) (hU : 0 ≤ U) (na nb : ℕ) (ha : 1 ≤ na) (hb : 1 ≤ nb) :
    (1+U)*(((na:ℝ)-1)*(1+U)^(na-1)+((nb:ℝ)-1)*(1+U)^(nb-1))+1 ≤
      ((na+nb:ℕ)-1:ℝ)*(1+U)^(na+nb-1) := by
  have h1 : (1:ℝ) ≤ 1+U := by linarith
  have pa : (1+U)*(1+U)^(na-1) ≤ (1+U)^(na+nb-1) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ h1 (by omega)
  have pb : (1+U)*(1+U)^(nb-1) ≤ (1+U)^(na+nb-1) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ h1 (by omega)
  have p1 : (1:ℝ) ≤ (1+U)^(na+nb-1) := one_le_pow₀ h1
  have hna : (1:ℝ) ≤ na := by exact_mod_cast ha
  have hnb : (1:ℝ) ≤ nb := by exact_mod_cast hb
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left pa (by linarith : (0:ℝ) ≤ na-1),
    mul_le_mul_of_nonneg_left pb (by linarith : (0:ℝ) ≤ nb-1)]

/-- Every association of a sum chain: if its leaves are `Safe`, the chain is,
and its running bound plus its leaf magnitudes is at most
`(1+U)ⁿ⁻¹ (Σ Bᵢ + Σ|tᵢ|) + (n-1)(1+U)ⁿ⁻¹ η`. -/
theorem sum_bound (v E : ℕ → ℝ) : ∀ e : GExpr,
    (∀ p ∈ sumLeaves e, p.2.Safe v E ∧ 0 ≤ p.2.bound v E) →
    e.Safe v E ∧ 0 ≤ e.bound v E ∧
      e.bound v E+lmag v (sumLeaves e) ≤
        (1+U)^((sumLeaves e).length-1)*(lbnd v E (sumLeaves e)+lmag v (sumLeaves e))+
          (((sumLeaves e).length:ℝ)-1)*(1+U)^((sumLeaves e).length-1)*η
  | .add a b, h => by
    have hU := U_pos; have hη := η_pos
    obtain ⟨sa, ba, ha⟩ := sum_bound v E a fun p hp => h p (by simp [sumLeaves, hp])
    obtain ⟨sb, bb, hb⟩ := sum_bound v E b fun p hp => h p (by simp [sumLeaves, hp])
    have na := sumLeaves_length_pos a; have nb := sumLeaves_length_pos b
    have ea := abs_exact_le v a; have eb := abs_exact_le v b
    refine ⟨⟨sa, sb⟩, by simp only [bound]; positivity, ?_⟩
    simp only [sumLeaves, bound, List.length_append, lmag, lbnd, List.map_append,
      List.sum_append] at ha hb ⊢
    set n := (sumLeaves a).length+(sumLeaves b).length
    set A := (1+U)^((sumLeaves a).length-1)
    set B := (1+U)^((sumLeaves b).length-1)
    have hA : (1+U)*A ≤ (1+U)^(n-1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have hB : (1+U)*B ≤ (1+U)^(n-1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have he := eta_step U hU.le _ _ na nb
    have l1 : 0 ≤ (lbnd v E (sumLeaves a)+lmag v (sumLeaves a)) :=
      add_nonneg (lbnd_nonneg fun p hp => (h p (by simp [sumLeaves, hp])).2) (lmag_nonneg _ _)
    have l2 : 0 ≤ (lbnd v E (sumLeaves b)+lmag v (sumLeaves b)) :=
      add_nonneg (lbnd_nonneg fun p hp => (h p (by simp [sumLeaves, hp])).2) (lmag_nonneg _ _)
    simp only [lmag, lbnd] at l1 l2 ea eb
    nlinarith [mul_le_mul_of_nonneg_right hA l1, mul_le_mul_of_nonneg_right hB l2]
  | .sub a b, h => by
    have hU := U_pos; have hη := η_pos
    obtain ⟨sa, ba, ha⟩ := sum_bound v E a fun p hp => h p (by simp [sumLeaves, hp])
    obtain ⟨sb, bb, hb⟩ := sum_bound v E b fun p hp => h ⟨!p.1, p.2⟩ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))
    have na := sumLeaves_length_pos a; have nb := sumLeaves_length_pos b
    have ea := abs_exact_le v a; have eb := abs_exact_le v b
    refine ⟨⟨sa, sb⟩, by simp only [bound]; positivity, ?_⟩
    simp only [sumLeaves, bound, List.length_append, List.length_map]
    rw [show lmag v (sumLeaves a ++ (sumLeaves b).map fun p => (!p.1, p.2)) =
        lmag v (sumLeaves a)+lmag v (sumLeaves b) by simp [lmag, Function.comp_def],
      show lbnd v E (sumLeaves a ++ (sumLeaves b).map fun p => (!p.1, p.2)) =
        lbnd v E (sumLeaves a)+lbnd v E (sumLeaves b) by simp [lbnd, Function.comp_def]]
    set n := (sumLeaves a).length+(sumLeaves b).length
    set A := (1+U)^((sumLeaves a).length-1)
    set B := (1+U)^((sumLeaves b).length-1)
    have hA : (1+U)*A ≤ (1+U)^(n-1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have hB : (1+U)*B ≤ (1+U)^(n-1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by linarith) (by omega)
    have he := eta_step U hU.le _ _ na nb
    have l1 : 0 ≤ (lbnd v E (sumLeaves a)+lmag v (sumLeaves a)) :=
      add_nonneg (lbnd_nonneg fun p hp => (h p (by simp [sumLeaves, hp])).2) (lmag_nonneg _ _)
    have l2 : 0 ≤ (lbnd v E (sumLeaves b)+lmag v (sumLeaves b)) :=
      add_nonneg (lbnd_nonneg fun p hp => (h ⟨!p.1, p.2⟩ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))).2) (lmag_nonneg _ _)
    nlinarith [mul_le_mul_of_nonneg_right hA l1, mul_le_mul_of_nonneg_right hB l2]
  | .neg a, h => by
    obtain ⟨sa, ba, ha⟩ := sum_bound v E a fun p hp => h ⟨!p.1, p.2⟩ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    refine ⟨sa, ba, ?_⟩
    simp only [sumLeaves, bound, List.length_map, lmag_flip, lbnd_flip]
    exact ha
  | .input _, h | .const _, h | .mul _ _, h | .div _ _, h | .sqrt _, h | .max _ _, h
  | .min _ _, h | .lt _ _ _ _, h | .abs _, h | .invsqrt _, h | .exp _, h | .exp2 _, h
  | .log _, h | .log2 _, h | .inh _ _, h | .tanh _ _, h | .lt2 _ _ _ _, h | .sinS _, h
  | .cosS _, h | .scale _ _, h | .round _, h | .qsel _ _ _ _, h => by
    simp only [sumLeaves, List.mem_singleton, forall_eq] at h ⊢
    refine ⟨h.1, h.2, ?_⟩
    simp [lmag, lbnd]

/-! ### Reassociation -/

/-- `e'` evaluates the sum chains of `e` in any association and order, with
each leaf replaced by a reassociation of it; everything else keeps its form. -/
inductive RA : GExpr → GExpr → Prop
  | sum {e e' : GExpr} (he : IsSum e) (he' : IsSum e')
      (σ : Fin (sumLeaves e).length ≃ Fin (sumLeaves e').length)
      (hs : ∀ i, ((sumLeaves e')[σ i]).1 = ((sumLeaves e)[i]).1)
      (hl : ∀ i, RA ((sumLeaves e)[i]).2 ((sumLeaves e')[σ i]).2) : RA e e'
  | input (i : ℕ) : RA (.input i) (.input i)
  | const (c : ℚ) : RA (.const c) (.const c)
  | mul {a b a' b' : GExpr} : RA a a' → RA b b' → RA (.mul a b) (.mul a' b')
  | div {a b a' b' : GExpr} : RA a a' → RA b b' → RA (.div a b) (.div a' b')
  | sqrt {a a' : GExpr} : RA a a' → RA (.sqrt a) (.sqrt a')
  | max {a b a' b' : GExpr} : RA a a' → RA b b' → RA (.max a b) (.max a' b')
  | min {a b a' b' : GExpr} : RA a a' → RA b b' → RA (.min a b) (.min a' b')
  | lt {c a b c' a' b' : GExpr} (t : ℚ) : RA c c' → RA a a' → RA b b' →
      RA (.lt c t a b) (.lt c' t a' b')
  | abs {a a' : GExpr} : RA a a' → RA (.abs a) (.abs a')
  | invsqrt {a a' : GExpr} : RA a a' → RA (.invsqrt a) (.invsqrt a')
  | exp {a a' : GExpr} : RA a a' → RA (.exp a) (.exp a')
  | exp2 {a a' : GExpr} : RA a a' → RA (.exp2 a) (.exp2 a')
  | log {a a' : GExpr} : RA a a' → RA (.log a) (.log a')
  | log2 {a a' : GExpr} : RA a a' → RA (.log2 a) (.log2 a')
  | inh (f : GExpr) {a a' : GExpr} : RA a a' → RA (.inh f a) (.inh f a')
  | tanh (f : GExpr) {a a' : GExpr} : RA a a' → RA (.tanh f a) (.tanh f a')
  | lt2 {a b x y a' b' x' y' : GExpr} : RA a a' → RA b b' → RA x x' → RA y y' →
      RA (.lt2 a b x y) (.lt2 a' b' x' y')
  | sinS {a a' : GExpr} : RA a a' → RA (.sinS a) (.sinS a')
  | cosS {a a' : GExpr} : RA a a' → RA (.cosS a) (.cosS a')
  | scale (k : ℤ) {a a' : GExpr} : RA a a' → RA (.scale k a) (.scale k a')
  | round {a a' : GExpr} : RA a a' → RA (.round a) (.round a')
  | qsel (j : Bool) {k s c k' s' c' : GExpr} : RA k k' → RA s s' → RA c c' →
      RA (.qsel j k s c) (.qsel j k' s' c')

lemma list_sum_fin {α : Type*} (L : List α) (f : α → ℝ) :
    (L.map f).sum = ∑ i : Fin L.length, f L[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]; rfl

/-- Reassociation does not change the exact value. -/
theorem exact_RA (v : ℕ → ℝ) {e e' : GExpr} (h : RA e e') : e'.exact v = e.exact v := by
  induction h with
  | sum he he' σ hs hl ih =>
    rename_i e e''
    rw [sum_exact v e, sum_exact v e'', list_sum_fin, list_sum_fin]
    rw [← Equiv.sum_comp σ]
    congr 1; ext i; rw [hs i, ih i]
  | input i => rfl
  | const c => rfl
  | mul _ _ iha ihb => simp only [exact, iha, ihb]
  | div _ _ iha ihb => simp only [exact, iha, ihb]
  | sqrt _ iha => simp only [exact, iha]
  | max _ _ iha ihb => simp only [exact, iha, ihb]
  | min _ _ iha ihb => simp only [exact, iha, ihb]
  | lt t _ _ _ ihc iha ihb => simp only [exact, ihc, iha, ihb]
  | abs _ iha => simp only [exact, iha]
  | invsqrt _ iha => simp only [exact, iha]
  | exp _ iha => simp only [exact, iha]
  | exp2 _ iha => simp only [exact, iha]
  | log _ iha => simp only [exact, iha]
  | log2 _ iha => simp only [exact, iha]
  | inh f _ iha => simp only [exact, iha]
  | tanh f _ iha => simp only [exact, iha]
  | lt2 _ _ _ _ iha ihb ihx ihy => simp only [exact, iha, ihb, ihx, ihy]
  | sinS _ iha => simp only [exact, iha]
  | cosS _ iha => simp only [exact, iha]
  | scale k _ iha => simp only [exact, iha]
  | round _ iha => simp only [exact, iha]
  | qsel j _ _ _ ihk ihs ihc => simp only [exact, ihk, ihs, ihc]

/-- Subterms are smaller. -/
macro "size_tac" : tactic => `(tactic| (simp only [GExpr.add.sizeOf_spec, GExpr.sub.sizeOf_spec, GExpr.mul.sizeOf_spec, GExpr.neg.sizeOf_spec, GExpr.div.sizeOf_spec, GExpr.sqrt.sizeOf_spec, GExpr.max.sizeOf_spec, GExpr.min.sizeOf_spec, GExpr.lt.sizeOf_spec, GExpr.abs.sizeOf_spec, GExpr.invsqrt.sizeOf_spec, GExpr.exp.sizeOf_spec, GExpr.exp2.sizeOf_spec, GExpr.log.sizeOf_spec, GExpr.log2.sizeOf_spec, GExpr.inh.sizeOf_spec, GExpr.tanh.sizeOf_spec, GExpr.lt2.sizeOf_spec, GExpr.sinS.sizeOf_spec, GExpr.cosS.sizeOf_spec, GExpr.scale.sizeOf_spec, GExpr.round.sizeOf_spec, GExpr.qsel.sizeOf_spec]; omega))

set_option linter.unusedSimpArgs false in
/-- Every program is a reassociation of itself. -/
theorem RA.refl (e : GExpr) : RA e e := by
  induction e using WellFounded.induction (measure (sizeOf : GExpr → ℕ)).wf with
  | _ e ih =>
    have ih' : ∀ x : GExpr, sizeOf x < sizeOf e → RA x x := ih
    by_cases hs : IsSum e
    · exact RA.sum hs hs (Equiv.refl _) (fun _ => rfl)
        fun i => ih' _ (sumLeaves_size e hs _ (List.getElem_mem _))
    · cases e with
      | add a b => exact absurd trivial hs
      | sub a b => exact absurd trivial hs
      | neg a => exact absurd trivial hs
      | input i => exact .input i
      | const c => exact .const c
      | mul a b => exact .mul (ih' a (by size_tac)) (ih' b (by size_tac))
      | div a b => exact .div (ih' a (by size_tac)) (ih' b (by size_tac))
      | sqrt a => exact .sqrt (ih' a (by size_tac))
      | max a b => exact .max (ih' a (by size_tac)) (ih' b (by size_tac))
      | min a b => exact .min (ih' a (by size_tac)) (ih' b (by size_tac))
      | lt c t a b =>
        exact .lt t (ih' c (by size_tac)) (ih' a (by size_tac)) (ih' b (by size_tac))
      | abs a => exact .abs (ih' a (by size_tac))
      | invsqrt a => exact .invsqrt (ih' a (by size_tac))
      | exp a => exact .exp (ih' a (by size_tac))
      | exp2 a => exact .exp2 (ih' a (by size_tac))
      | log a => exact .log (ih' a (by size_tac))
      | log2 a => exact .log2 (ih' a (by size_tac))
      | inh f a => exact .inh f (ih' a (by size_tac))
      | tanh f a => exact .tanh f (ih' a (by size_tac))
      | lt2 a b x y =>
        exact .lt2 (ih' a (by size_tac)) (ih' b (by size_tac)) (ih' x (by size_tac))
          (ih' y (by size_tac))
      | sinS a => exact .sinS (ih' a (by size_tac))
      | cosS a => exact .cosS (ih' a (by size_tac))
      | scale k a => exact .scale k (ih' a (by size_tac))
      | round a => exact .round (ih' a (by size_tac))
      | qsel j k s c =>
        exact .qsel j (ih' k (by size_tac)) (ih' s (by size_tac)) (ih' c (by size_tac))

/-- A reassociation of a sum chain is a sum chain whose leaves are the
reassociated leaves, permuted. -/
lemma RA.sum_inv {e e' : GExpr} (h : RA e e') (he : IsSum e) :
    ∃ (_ : IsSum e') (σ : Fin (sumLeaves e).length ≃ Fin (sumLeaves e').length),
      (∀ i, ((sumLeaves e')[σ i]).1 = ((sumLeaves e)[i]).1) ∧
      ∀ i, RA ((sumLeaves e)[i]).2 ((sumLeaves e')[σ i]).2 := by
  cases h with
  | sum _ he' σ hs hl => exact ⟨he', σ, hs, hl⟩
  | _ => simp_all [IsSum]

lemma RA.input_inv {i : ℕ} {x' : GExpr} (h : RA (.input i) x') : x' = .input i := by
  cases h with
  | sum he => exact absurd he (by simp [IsSum])
  | input => rfl

lemma RA.const_inv {c : ℚ} {x' : GExpr} (h : RA (.const c) x') : x' = .const c := by
  cases h with
  | sum he => exact absurd he (by simp [IsSum])
  | const => rfl

end BlackHole.WgslReassoc
