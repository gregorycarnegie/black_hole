module
public import BlackHole.CheckedFunction
public import BlackHole.KerrProgramFast

/-! Numerical certificate evaluation with no real-valued function fields.
Erasure commutes with every operation and with the full Kerr program, so a
single successful box computation applies to every enclosed real input. -/

@[expose] public section
noncomputable section
open Set
open scoped Topology
namespace BlackHole.CheckedData
open DyadicInterval IntervalJet NormalizedJet

abbrev Data := Option (ℕ → Bounds)

def erase (a : CheckedFunction.Approx N s) : Data := a.certificate.map (fun c => c.data)

def constant (q : Dyadic) : Data := some (fun k => if k=0 then ⟨q,q⟩ else ⟨0,0⟩)

def add (N : ℕ) (proposal : (ℕ → Bounds) → (ℕ → Bounds) → Array Bounds) (a b : Data) : Data :=
  match a,b with
  | some a,some b =>
    let c := CheckedFunction.lookup (proposal a b)
    if additionCheck a b c N = true then some c else none
  | _,_ => none

def neg (a : Data) : Data := a.map (fun a k => negate (a k))

def mul (N : ℕ) (proposal : (ℕ → Bounds) → (ℕ → Bounds) → Array ConvolutionRow) (a b : Data) : Data :=
  match a,b with
  | some a,some b =>
    let row := CheckedFunction.rowAt (proposal a b)
    if multiplicationCheck a b row N = true then some (fun k => (row k).accum (k+1)) else none
  | _,_ => none

def div (N : ℕ) (proposal : (ℕ → Bounds) → (ℕ → Bounds) → CheckedFunction.DivisionProposal)
    (a b : Data) : Data :=
  match a,b with
  | some a,some b =>
    let p := proposal a b
    if quotientCheck a b p.result p.row N = true then some p.result else none
  | _,_ => none

def sqrt (N : ℕ) (proposal : (ℕ → Bounds) → CheckedFunction.RootProposal) (a : Data) : Data :=
  match a with
  | some a =>
    let p := proposal a
    if (decide ((0:Dyadic) < (a 0).lo) && rootCheck a p.result p.row N) = true then some p.result else none
  | none => none

def operations (p : CheckedFunction.Proposals) (N : ℕ) : KerrProgram.Operations Data := {
  constant := constant
  add := add N p.addition
  sub := fun a b => add N p.addition a (neg b)
  mul := mul N p.multiplication
  div := div N p.division
  neg := neg
  sqrt := sqrt N p.root }

theorem erase_constant (s : Set ℝ) (q : Dyadic) :
    erase (CheckedFunction.constant (N := N) s q) = constant q := rfl

theorem erase_add (proposal) (a b : CheckedFunction.Approx N s) :
    erase (CheckedFunction.add proposal a b) = add N proposal (erase a) (erase b) := by
  cases ha : a.certificate with
  | none => simp [CheckedFunction.add,erase,add,ha]
  | some ca =>
    cases hb : b.certificate with
    | none => simp [CheckedFunction.add,erase,add,ha,hb]
    | some cb =>
      by_cases hc : additionCheck ca.data cb.data (CheckedFunction.lookup (proposal ca.data cb.data)) N = true <;>
        simp [CheckedFunction.add,erase,add,ha,hb,hc]

theorem erase_neg (a : CheckedFunction.Approx N s) : erase (CheckedFunction.neg a) = neg (erase a) := by
  cases ha : a.certificate <;> simp [CheckedFunction.neg,erase,neg,ha]

theorem erase_mul (proposal) (a b : CheckedFunction.Approx N s) :
    erase (CheckedFunction.mul proposal a b) = mul N proposal (erase a) (erase b) := by
  cases ha : a.certificate with
  | none => simp [CheckedFunction.mul,erase,mul,ha]
  | some ca =>
    cases hb : b.certificate with
    | none => simp [CheckedFunction.mul,erase,mul,ha,hb]
    | some cb =>
      by_cases hc : multiplicationCheck ca.data cb.data (CheckedFunction.rowAt (proposal ca.data cb.data)) N = true <;>
        simp [CheckedFunction.mul,erase,mul,ha,hb,hc]

theorem erase_div (proposal) (a b : CheckedFunction.Approx N s) :
    erase (CheckedFunction.div proposal a b) = div N proposal (erase a) (erase b) := by
  cases ha : a.certificate with
  | none => simp [CheckedFunction.div,erase,div,ha]
  | some ca =>
    cases hb : b.certificate with
    | none => simp [CheckedFunction.div,erase,div,ha,hb]
    | some cb =>
      by_cases hc : quotientCheck ca.data cb.data (proposal ca.data cb.data).result
          (proposal ca.data cb.data).row N = true <;>
        simp [CheckedFunction.div,erase,div,ha,hb,hc]

theorem erase_sqrt (proposal) (a : CheckedFunction.Approx N s) :
    erase (CheckedFunction.sqrt proposal a) = sqrt N proposal (erase a) := by
  cases ha : a.certificate with
  | none => simp [CheckedFunction.sqrt,erase,sqrt,ha]
  | some ca =>
    by_cases hc : (decide ((0:Dyadic) < (ca.data 0).lo) &&
        rootCheck ca.data (proposal ca.data).result (proposal ca.data).row N) = true <;>
      simp [CheckedFunction.sqrt,erase,sqrt,ha,hc]

theorem operations_map (p : CheckedFunction.Proposals) (s : Set ℝ) :
    KerrProgram.OperationMap (CheckedFunction.operations (N := N) p s) (operations p N) erase := by
  constructor
  · intro q; rfl
  · intro a b; exact erase_add _ a b
  · intro a b
    change erase (CheckedFunction.add _ a (CheckedFunction.neg b)) = _
    rw [erase_add,erase_neg]; rfl
  · intro a b; exact erase_mul _ a b
  · intro a b; exact erase_div _ a b
  · intro a; exact erase_neg a
  · intro a; exact erase_sqrt _ a

def execute (p : CheckedFunction.Proposals) (N : ℕ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State Data) : KerrProgram.State Data :=
  KerrProgram.rhsFast (operations p N) (fun i => constant (spin i)) input

theorem erase_execute (p : CheckedFunction.Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (CheckedFunction.Approx N s)) :
    KerrProgram.mapState erase (CheckedFunction.execute p s spin input) =
      execute p N spin (KerrProgram.mapState erase input) := by
  rw [execute,KerrProgram.rhsFast_eq]
  exact KerrProgram.map_rhs (operations_map p s) (fun i => CheckedFunction.constant s (spin i)) input

theorem mapState_get (state : KerrProgram.State (CheckedFunction.Approx N s))
    (c : KerrProgram.Component) :
    (KerrProgram.mapState erase state).get c = erase (state.get c) := by cases c <;> rfl

theorem certificate_of_data (p : CheckedFunction.Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (CheckedFunction.Approx N s)) (component : KerrProgram.Component)
    (d : ℕ → Bounds)
    (hd : (execute p N spin (KerrProgram.mapState erase input)).get component = some d) :
    ∃ c : CheckedFunction.Certificate N s ((CheckedFunction.execute p s spin input).get component).fn,
      c.data = d := by
  rw [← erase_execute, mapState_get] at hd
  unfold erase at hd
  cases hc : ((CheckedFunction.execute p s spin input).get component).certificate with
  | none => simp [hc] at hd
  | some c =>
    simp only [hc,Option.map_some,Option.some.injEq] at hd
    exact ⟨c,hd⟩

/-- The actual Kerr right-hand side along a real input, one component at a time. -/
def field (spin : Fin 3 → Dyadic) (input : KerrProgram.State (CheckedFunction.Approx N s))
    (component : KerrProgram.Component) (u : ℝ) : ℝ :=
  KerrProgram.phaseGet (KerrField.phaseRhs 1 (CheckedFunction.spinValue spin)
    (CheckedFunction.inputAt input u)) component

/-- One successful data-only evaluation encloses the Taylor coefficients of
the actual Kerr field along every real input whose certificates erase to the
same data, and shows that field is smooth there. -/
theorem rhs_enclosure (p : CheckedFunction.Proposals) (s : Set ℝ) (spin : Fin 3 → Dyadic)
    (input : KerrProgram.State (CheckedFunction.Approx N s)) (component : KerrProgram.Component)
    (d : ℕ → Bounds)
    (hd : (execute p N spin (KerrProgram.mapState erase input)).get component = some d)
    (t : ℝ) (ht : t ∈ s)
    (hpos : ContinuousAt (fun u => (CheckedFunction.inputAt input u).1) t)
    (hr : 0 < Cartesian.radius (CheckedFunction.spinValue spin) (CheckedFunction.inputAt input t).1) :
    ContDiffAt ℝ N (field spin input component) t ∧
      ∀ n ≤ N, Contains (d n) (coefficient (field spin input component) n t) := by
  obtain ⟨c,rfl⟩ := certificate_of_data p s spin input component d hd
  have heq : ((CheckedFunction.execute p s spin input).get component).fn =ᶠ[𝓝 t]
      field spin input component := by
    filter_upwards [CheckedFunction.execute_eventually p s spin input t hpos hr] with u hu
    simpa only [field,KerrProgram.map_get] using congrArg (fun state => KerrProgram.phaseGet state component) hu
  exact ⟨(c.smooth t ht).congr_of_eventuallyEq heq.symm,
    fun n hn => CheckedFunction.rhs_coefficient p s spin input component c t ht n hn hpos hr⟩

/-- Distance from a real proposal coefficient to everything in an interval. -/
def gap (a : ℝ) (b : Bounds) : ℝ := max |a-b.lo.toReal| |a-b.hi.toReal|

theorem gap_sound {a x : ℝ} {b : Bounds} (hx : Contains b x) : |a-x| ≤ gap a b := by
  obtain ⟨hlo,hhi⟩ := hx
  unfold gap
  rcases le_total a x with h | h
  · rw [abs_of_nonpos (by linarith),abs_sub_comm a b.hi.toReal]
    exact le_max_of_le_right ((by linarith : -(a-x) ≤ b.hi.toReal-a).trans (le_abs_self _))
  · rw [abs_of_nonneg (by linarith)]
    exact le_max_of_le_left ((by linarith : a-x ≤ a-b.lo.toReal).trans (le_abs_self _))

/-- Point coefficients at the step start and one box bound on the fourth
coefficient give a residual bound for the cubic derivative of the quartic
proposal, uniformly over the step. -/
theorem residual_of_bounds (g : ℝ → ℝ) (a : Fin 4 → ℝ) (h : ℝ) (point : ℕ → Bounds) (box : Bounds)
    (hh : 0 < h) (hg : ∀ t ∈ Icc 0 h, ContDiffAt ℝ 4 g t)
    (hpoint : ∀ k < 4, Contains (point k) (coefficient g k 0))
    (hbox : ∀ t ∈ Icc 0 h, Contains box (coefficient g 4 t))
    (t : ℝ) (ht : t ∈ Icc 0 h) :
    |(∑ k : Fin 4, a k*t^(k:ℕ))-g t| ≤
      (∑ k : Fin 4, gap (a k) (point k)*h^(k:ℕ))+4*gap 0 box*h^4 := by
  have hB : 0 ≤ gap 0 box := (abs_nonneg _).trans (le_max_left _ _)
  have hfour (u : ℝ) (hu : u ∈ Icc 0 h) : |coefficient g 4 u| ≤ gap 0 box := by
    simpa using gap_sound (a := 0) (hbox u hu)
  refine (NormalizedJet.cubic_residual_bound g a h _ hh hB hg hfour t ht).trans ?_
  gcongr with k
  exact gap_sound (hpoint k k.2)

/-- The residual of one Kerr component along a quartic proposal is bounded by
two data-only evaluations: one at the step start and one over the whole step. -/
theorem kerr_residual (p : CheckedFunction.Proposals) (spin : Fin 3 → Dyadic) (h : ℝ) (hh : 0 < h)
    (s0 : Set ℝ) (hs0 : (0:ℝ) ∈ s0)
    (start : KerrProgram.State (CheckedFunction.Approx 4 s0))
    (step : KerrProgram.State (CheckedFunction.Approx 4 (Icc 0 h)))
    (hsame : CheckedFunction.inputAt start = CheckedFunction.inputAt step)
    (component : KerrProgram.Component) (point boxData : ℕ → Bounds)
    (hpoint : (execute p 4 spin (KerrProgram.mapState erase start)).get component = some point)
    (hbox : (execute p 4 spin (KerrProgram.mapState erase step)).get component = some boxData)
    (hpos : ∀ t ∈ Icc 0 h, ContinuousAt (fun u => (CheckedFunction.inputAt step u).1) t)
    (hr : ∀ t ∈ Icc 0 h,
      0 < Cartesian.radius (CheckedFunction.spinValue spin) (CheckedFunction.inputAt step t).1)
    (a : Fin 4 → ℝ) (t : ℝ) (ht : t ∈ Icc 0 h) :
    |(∑ k : Fin 4, a k*t^(k:ℕ))-field spin step component t| ≤
      (∑ k : Fin 4, gap (a k) (point k)*h^(k:ℕ))+4*gap 0 (boxData 4)*h^4 := by
  have h0 : (0:ℝ) ∈ Icc 0 h := ⟨le_rfl,hh.le⟩
  have hfield : field spin start component = field spin step component := by
    funext u; simp only [field,hsame]
  have hs := rhs_enclosure p _ spin start component point hpoint 0 hs0
    (by simpa only [hsame] using hpos 0 h0) (by simpa only [hsame] using hr 0 h0)
  rw [hfield] at hs
  apply residual_of_bounds _ a h point (boxData 4) hh
    (fun u hu => (rhs_enclosure p _ spin step component boxData hbox u hu (hpos u hu) (hr u hu)).1)
    (fun k hk => hs.2 k hk.le)
    (fun u hu => (rhs_enclosure p _ spin step component boxData hbox u hu (hpos u hu) (hr u hu)).2 4 le_rfl)
    t ht

end BlackHole.CheckedData
