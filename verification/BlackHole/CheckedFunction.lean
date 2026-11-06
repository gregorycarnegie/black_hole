module
public import BlackHole.IntervalJet
public import BlackHole.KerrProgram

/-! Proof-carrying arithmetic for the complete source evaluator. Failed
finite dyadic checks erase the certificate; successful operations derive
both smoothness and derivative bounds from their inputs. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology
namespace BlackHole.CheckedFunction
open DyadicInterval IntervalJet NormalizedJet

structure Certificate (N : ℕ) (s : Set ℝ) (f : ℝ → ℝ) where
  data : ℕ → Bounds
  smooth : ∀ t ∈ s, ContDiffAt ℝ N f t
  encloses : ∀ t ∈ s, Encloses data f N t

structure Approx (N : ℕ) (s : Set ℝ) where
  fn : ℝ → ℝ
  certificate : Option (Certificate N s fn)

variable {N : ℕ}

/-- Materialized coefficient tables. Proposals return arrays so executable
evaluation never recomputes a shared subexpression through a closure. -/
def lookup (c : Array Bounds) (k : ℕ) : Bounds := c.getD k ⟨0,0⟩

def rowAt (rows : Array ConvolutionRow) (k : ℕ) : ConvolutionRow :=
  rows.getD k ⟨fun _ => ⟨0,0⟩,fun _ => ⟨0,0⟩⟩

def constant (s : Set ℝ) (q : Dyadic) : Approx N s where
  fn := fun _ => q.toReal
  certificate := some {
    data := fun k => if k=0 then ⟨q,q⟩ else ⟨0,0⟩
    smooth := fun _ _ => contDiffAt_const
    encloses := by
      intro t _ k _
      by_cases hk : k=0
      · subst k; simp [Contains]
      · simp [hk,Contains,coefficient,iteratedDeriv_const] }

/-- A coordinate line through any point in a box supplies both its value
enclosure and its exact directional derivative for Jacobian evaluation. -/
def affineAtZero (base direction : ℝ) (value slope : Bounds)
    (hvalue : Contains value base) (hslope : Contains slope direction) : Approx N ({0}:Set ℝ) where
  fn := fun t => base+t*direction
  certificate := some {
    data := fun k => if k=0 then value else if k=1 then slope else ⟨0,0⟩
    smooth := fun _ _ => by fun_prop
    encloses := by
      intro t ht k _
      have ht0 : t=0 := Set.mem_singleton_iff.mp ht
      subst t
      rw [affine_coefficient]
      by_cases hk0 : k=0
      · simpa [hk0] using hvalue
      · by_cases hk1 : k=1
        · simpa [hk0,hk1] using hslope
        · simp [hk0,hk1,Contains] }

def time (lo hi : Dyadic) : Approx N (Icc lo.toReal hi.toReal) where
  fn := id
  certificate := some {
    data := fun k => if k=0 then ⟨lo,hi⟩ else if k=1 then ⟨1,1⟩ else ⟨0,0⟩
    smooth := fun _ _ => contDiffAt_id
    encloses := by
      intro t ht k _
      by_cases hk0 : k=0
      · subst k; simpa [Contains] using ht
      · by_cases hk1 : k=1
        · subst k; simp [coefficient,Contains]
        · simp [hk0,hk1,Contains,coefficient,iteratedDeriv_id] }

def add (proposal : (ℕ → Bounds) → (ℕ → Bounds) → Array Bounds)
    (a b : Approx N s) : Approx N s := by
  refine ⟨a.fn+b.fn,?_⟩
  match a.certificate,b.certificate with
  | some ca,some cb =>
    let c := lookup (proposal ca.data cb.data)
    exact if h : additionCheck ca.data cb.data c N = true then some {
      data := c
      smooth := fun t ht => (ca.smooth t ht).add (cb.smooth t ht)
      encloses := fun t ht => add_encloses (ca.smooth t ht) (cb.smooth t ht)
        (ca.encloses t ht) (cb.encloses t ht) ((additionCheck_true _ _ _ _).mp h) } else none
  | _,_ => exact none

def neg (a : Approx N s) : Approx N s where
  fn := -a.fn
  certificate := a.certificate.map fun ca => {
    data := fun k => negate (ca.data k)
    smooth := fun t ht => (ca.smooth t ht).neg
    encloses := by
      intro t ht k hk
      rw [coefficient_neg]
      exact neg_sound (ca.encloses t ht k hk) }

def mul (proposal : (ℕ → Bounds) → (ℕ → Bounds) → Array ConvolutionRow)
    (a b : Approx N s) : Approx N s := by
  refine ⟨a.fn*b.fn,?_⟩
  match a.certificate,b.certificate with
  | some ca,some cb =>
    let row := rowAt (proposal ca.data cb.data)
    exact if h : multiplicationCheck ca.data cb.data row N = true
      then some {
        data := fun k => (row k).accum (k+1)
        smooth := fun t ht => (ca.smooth t ht).mul (cb.smooth t ht)
        encloses := by
          intro t ht k hk
          have hc := (multiplicationCheck_true _ _ _ _).mp h k hk
          exact mul_component ((ca.smooth t ht).of_le (by exact_mod_cast hk))
            ((cb.smooth t ht).of_le (by exact_mod_cast hk))
            (fun i hi => ca.encloses t ht i (hi.trans hk))
            (fun i hi => cb.encloses t ht i (hi.trans hk))
            (row k) hc.1 hc.2.1 hc.2.2 } else none
  | _,_ => exact none

structure DivisionProposal where
  result : ℕ → Bounds
  row : ℕ → QuotientRow

def div (proposal : (ℕ → Bounds) → (ℕ → Bounds) → DivisionProposal)
    (a b : Approx N s) : Approx N s := by
  refine ⟨fun t => a.fn t/b.fn t,?_⟩
  match a.certificate,b.certificate with
  | some ca,some cb =>
    let p := proposal ca.data cb.data
    exact if h : quotientCheck ca.data cb.data p.result p.row N = true then
      let hspec := (quotientCheck_true _ _ _ _ _).mp h
      some {
      data := p.result
      smooth := by
        intro t ht
        have hn := reciprocal_nonzero (hspec 0 (Nat.zero_le N)).2.2.2.2.1
          (cb.encloses t ht 0 (Nat.zero_le N))
        simp only [coefficient_zero] at hn
        exact (ca.smooth t ht).div (cb.smooth t ht) hn
      encloses := by
        intro t ht
        have hn := reciprocal_nonzero (hspec 0 (Nat.zero_le N)).2.2.2.2.1
          (cb.encloses t ht 0 (Nat.zero_le N))
        simp only [coefficient_zero] at hn
        exact div_encloses (ca.smooth t ht) (cb.smooth t ht) hn
          (ca.encloses t ht) (cb.encloses t ht) p.row hspec } else none
  | _,_ => exact none

structure RootProposal where
  result : ℕ → Bounds
  row : ℕ → RootRow

def sqrt (proposal : (ℕ → Bounds) → RootProposal) (a : Approx N s) : Approx N s := by
  refine ⟨fun t => Real.sqrt (a.fn t),?_⟩
  match a.certificate with
  | some ca =>
    let p := proposal ca.data
    exact if h : (decide ((0:Dyadic) < (ca.data 0).lo) && rootCheck ca.data p.result p.row N) = true then
      let hchecks : decide ((0:Dyadic) < (ca.data 0).lo) = true ∧
          rootCheck ca.data p.result p.row N = true := by simpa only [Bool.and_eq_true] using h
      let hpositive := of_decide_eq_true hchecks.1
      let hspec := (rootCheck_true _ _ _ _).mp hchecks.2
      some {
      data := p.result
      smooth := by
        intro t ht
        have hl : 0 < (ca.data 0).lo.toReal := by simpa using Dyadic.toReal_lt_toReal.mpr hpositive
        have hv := (ca.encloses t ht 0 (Nat.zero_le N)).1
        simp only [coefficient_zero] at hv
        exact (ca.smooth t ht).sqrt (ne_of_gt (hl.trans_le hv))
      encloses := by
        intro t ht
        have hl : 0 < (ca.data 0).lo.toReal := by simpa using Dyadic.toReal_lt_toReal.mpr hpositive
        have hv := (ca.encloses t ht 0 (Nat.zero_le N)).1
        simp only [coefficient_zero] at hv
        exact sqrt_encloses (ca.smooth t ht) (hl.trans_le hv) (ca.encloses t ht) p.row hspec } else none
  | none => exact none

structure Proposals where
  addition : (ℕ → Bounds) → (ℕ → Bounds) → Array Bounds
  multiplication : (ℕ → Bounds) → (ℕ → Bounds) → Array ConvolutionRow
  division : (ℕ → Bounds) → (ℕ → Bounds) → DivisionProposal
  root : (ℕ → Bounds) → RootProposal

def operations (p : Proposals) (s : Set ℝ) : KerrProgram.Operations (Approx N s) := {
  constant := constant s
  add := add p.addition
  sub := fun a b => add p.addition a (neg b)
  mul := mul p.multiplication
  div := div p.division
  neg := neg
  sqrt := sqrt p.root }

/-- Evaluating a proof-carrying value always has the ordinary real meaning,
even when a certificate failed. The failed value cannot supply bounds. -/
theorem operations_semantics (p : Proposals) (s : Set ℝ) (t : ℝ) :
    KerrProgram.Semantics (operations (N := N) p s) (fun a => a.fn t) := by
  constructor
  · intro q; rfl
  · intro a b; rfl
  · intro a b
    change a.fn t+-b.fn t = a.fn t-b.fn t
    exact (sub_eq_add_neg _ _).symm
  · intro a b; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro a; rfl

def spinValue (spin : Fin 3 → Dyadic) : Cartesian.Space := fun i => (spin i).toReal

def inputAt (input : KerrProgram.State (Approx N s)) (t : ℝ) : KerrField.Phase :=
  KerrProgram.toPhase (KerrProgram.mapState (fun a => a.fn t) input)

def execute (p : Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (Approx N s)) : KerrProgram.State (Approx N s) :=
  KerrProgram.rhs (operations p s) (fun i => constant s (spin i)) input

theorem execute_value (p : Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (Approx N s)) (t : ℝ)
    (hr : 0 < Cartesian.radius (spinValue spin) (inputAt input t).1) :
    KerrProgram.toPhase (KerrProgram.mapState (fun a => a.fn t) (execute p s spin input)) =
      KerrField.phaseRhs 1 (spinValue spin) (inputAt input t) := by
  have hm := congrArg KerrProgram.toPhase
    (KerrProgram.map_rhs (operations_semantics p s t) (fun i => constant s (spin i)) input)
  exact hm.trans (KerrProgram.real_rhs_exact _ _ hr)

theorem execute_eventually (p : Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (Approx N s)) (t : ℝ)
    (hpos : ContinuousAt (fun u => (inputAt input u).1) t)
    (hr : 0 < Cartesian.radius (spinValue spin) (inputAt input t).1) :
    (fun u => KerrProgram.toPhase (KerrProgram.mapState (fun a => a.fn u) (execute p s spin input)))
      =ᶠ[𝓝 t] (fun u => KerrField.phaseRhs 1 (spinValue spin) (inputAt input u)) := by
  have hcont : ContinuousAt (fun u : ℝ => Cartesian.radius (spinValue spin) (inputAt input u).1) t :=
    ContinuousAt.comp (f := fun u : ℝ => (inputAt input u).1) (g := Cartesian.radius (spinValue spin))
      (Cartesian.radius_smooth (spinValue spin) (inputAt input t).1 hr).continuousAt hpos
  have hnear := hcont.eventually (eventually_gt_nhds hr)
  filter_upwards [hnear] with u hu
  exact execute_value p s spin input u hu

/-- Successful source evaluation supplies actual Kerr derivative enclosures.
No local defect or Jacobian bound is assumed by this theorem. -/
theorem rhs_coefficient (p : Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (Approx N s)) (component : KerrProgram.Component)
    (c : Certificate N s ((execute p s spin input).get component).fn)
    (t : ℝ) (ht : t ∈ s) (n : ℕ) (hn : n ≤ N)
    (hpos : ContinuousAt (fun u => (inputAt input u).1) t)
    (hr : 0 < Cartesian.radius (spinValue spin) (inputAt input t).1) :
    Contains (c.data n) (coefficient
      (fun u => KerrProgram.phaseGet (KerrField.phaseRhs 1 (spinValue spin) (inputAt input u)) component) n t) := by
  have heq : ((execute p s spin input).get component).fn =ᶠ[𝓝 t]
      (fun u => KerrProgram.phaseGet (KerrField.phaseRhs 1 (spinValue spin) (inputAt input u)) component) := by
    filter_upwards [execute_eventually p s spin input t hpos hr] with u hu
    have hcomponent := congrArg (fun state => KerrProgram.phaseGet state component) hu
    simpa only [KerrProgram.map_get] using hcomponent
  rw [← coefficient_congr heq]
  exact c.encloses t ht n hn

end BlackHole.CheckedFunction
