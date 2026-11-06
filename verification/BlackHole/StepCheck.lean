module
public import BlackHole.StepField
public import BlackHole.CheckedData
public import BlackHole.RoundedProposals
public import Mathlib.Analysis.ODE.Gronwall

/-! An executable checker for one certified Kerr step. The proposal (step
length, quartic coefficients, weights and tube radius) comes from an
untrusted search. The checker recomputes every bound with checked dyadic
interval jets, and `check_sound` turns success into an exact solution of the
Kerr equations that stays inside the reported tube and ends in the reported
box, for every initial point and time momentum in the input boxes. -/

@[expose] public section
open Set
open scoped Topology
namespace BlackHole.StepCheck
open DyadicInterval IntervalJet NormalizedJet KerrProgram StepField

/-! ### Exact dyadic helpers -/

def dmax (a b : Dyadic) : Dyadic := if a ≤ b then b else a
def mag (a : Dyadic) : Dyadic := dmax a (-a)
def gapD (a : Dyadic) (b : Bounds) : Dyadic := dmax (mag (a-b.lo)) (mag (a-b.hi))
def maxOf (f : Fin 10 → Dyadic) : Dyadic := (List.finRange 10).foldl (fun m i => dmax m (f i)) 0
def divUp (prec : ℕ) (x y : Dyadic) : Dyadic := Dyadic.divAtPrec x y prec+Dyadic.ofIntWithPrec 1 prec

theorem toReal_sub (a b : Dyadic) : (a-b).toReal = a.toReal-b.toReal := by
  rw [show a-b = a+-b from rfl,Dyadic.toReal_add,real_neg,sub_eq_add_neg]

theorem toReal_dmax (a b : Dyadic) : (dmax a b).toReal = max a.toReal b.toReal := by
  unfold dmax
  split_ifs with h
  · exact (max_eq_right (Dyadic.toReal_le_toReal.mpr h)).symm
  · exact (max_eq_left (Dyadic.toReal_le_toReal.mpr (le_of_not_ge h))).symm

theorem toReal_mag (a : Dyadic) : (mag a).toReal = |a.toReal| := by
  rw [mag,toReal_dmax,real_neg,abs_eq_max_neg]

theorem toReal_gapD (a : Dyadic) (b : Bounds) : (gapD a b).toReal = CheckedData.gap a.toReal b := by
  simp [gapD,CheckedData.gap,toReal_dmax,toReal_mag,toReal_sub]

/-- `Option` guard on a computed Boolean. -/
def require (b : Bool) : Option Unit := if b then some () else none

theorem require_some {b : Bool} {u : Unit} (h : require b = some u) : b = true := by
  unfold require at h
  split_ifs at h with hb
  exact hb

/-- All ten values, each evaluated exactly once. -/
def collect {α : Type*} (f : Fin 10 → Option α) : Option (Fin 10 → α) :=
  let v := Vector.ofFn f
  if h : ∀ i, (v.get i).isSome then some (fun i => (v.get i).get (h i)) else none

theorem collect_some {α : Type*} {f : Fin 10 → Option α} {g : Fin 10 → α}
    (h : collect f = some g) (i : Fin 10) : f i = some (g i) := by
  dsimp only [collect] at h
  split_ifs at h with hs
  cases h
  rw [← KerrProgram.vector_get_ofFn f i]
  exact Option.eq_some_of_isSome (hs i)

/-- The ten integrated components of a checked state; its argument is
evaluated once, before any component is read. -/
def components (st : State CheckedData.Data) : Fin 10 → CheckedData.Data :=
  fun i => st.get (component i)

/-! ### Programs shared by real and checked evaluation -/

def horner {S : Type*} (op : Operations S) (A : Fin 5 → Dyadic) (t : S) : S :=
  op.add (op.constant (A 0)) (op.mul t (op.add (op.constant (A 1)) (op.mul t
    (op.add (op.constant (A 2)) (op.mul t (op.add (op.constant (A 3))
      (op.mul t (op.constant (A 4)))))))))

def stepInput {S : Type*} (op : Operations S) (A : Fin 10 → Fin 5 → Dyadic) (t pt : S) : State S :=
  assemble pt (fun i => horner op (A i) t)

theorem map_horner {S T : Type*} {op : Operations S} {target : Operations T} {eval : S → T}
    (h : OperationMap op target eval) (A : Fin 5 → Dyadic) (t : S) :
    eval (horner op A t) = horner target A (eval t) := by
  simp [horner,h.add,h.mul,h.constant]

theorem map_radius {S T : Type*} {op : Operations S} {target : Operations T} {eval : S → T}
    (h : OperationMap op target eval) (a x : Fin 3 → S) :
    eval (radius op a x) = radius target (fun i => eval (a i)) (fun i => eval (x i)) := by
  simp [radius,dot3,map_sum3 h,h.add,h.sub,h.mul,h.div,h.sqrt,h.constant]

def poly (A : Fin 10 → Fin 5 → Dyadic) (t : ℝ) : Reduced :=
  fun i => (A i 0).toReal+t*((A i 1).toReal+t*((A i 2).toReal+t*((A i 3).toReal+t*(A i 4).toReal)))

def polyDeriv (A : Fin 10 → Fin 5 → Dyadic) (t : ℝ) : Reduced :=
  fun i => ∑ k : Fin 4, (((k:ℕ):ℝ)+1)*(A i k.succ).toReal*t^(k:ℕ)

theorem real_horner (A : Fin 5 → Dyadic) (t : ℝ) :
    horner realOperations A t = (A 0).toReal+t*((A 1).toReal+t*((A 2).toReal+t*((A 3).toReal+t*(A 4).toReal))) := rfl

theorem poly_hasDerivAt (A : Fin 10 → Fin 5 → Dyadic) (t : ℝ) :
    HasDerivAt (poly A) (polyDeriv A t) t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  have h := ((((((hasDerivAt_id t).mul_const ((A i 4).toReal)).const_add ((A i 3).toReal)).mul
    (hasDerivAt_id t)).const_add ((A i 2).toReal)).mul (hasDerivAt_id t)).const_add ((A i 1).toReal)
  have h2 := (h.mul (hasDerivAt_id t)).const_add ((A i 0).toReal)
  convert h2 using 1
  · funext u; simp [poly]; ring
  · simp [polyDeriv,Fin.sum_univ_four]; ring

theorem polyDeriv_continuous (A : Fin 10 → Fin 5 → Dyadic) : Continuous (polyDeriv A) := by
  unfold polyDeriv; fun_prop

/-! ### Checked inputs -/

def boxD (b : Bounds) : CheckedData.Data := some (fun k => if k=0 then b else ⟨0,0⟩)
def timeD (lo hi : Dyadic) : CheckedData.Data :=
  some (fun k => if k=0 then ⟨lo,hi⟩ else if k=1 then ⟨1,1⟩ else ⟨0,0⟩)
def lineD (value slope : Bounds) : CheckedData.Data :=
  some (fun k => if k=0 then value else if k=1 then slope else ⟨0,0⟩)

def unit (j k : Fin 10) : Bounds := if k=j then ⟨1,1⟩ else ⟨0,0⟩

def ops (prec N : ℕ) := CheckedData.operations (RoundedProposals.proposals prec N) N
def run (prec N : ℕ) (spin : Fin 3 → Dyadic) (input : State CheckedData.Data) : State CheckedData.Data :=
  CheckedData.execute (RoundedProposals.proposals prec N) N spin input

/-! ### The step proposal and its checker -/

structure Step where
  h : Dyadic
  A : Fin 10 → Fin 5 → Dyadic
  w : Fin 10 → Dyadic
  rho : Dyadic

structure Result where
  e0 : Dyadic
  defect : Dyadic
  lipschitz : Dyadic
  tube : Fin 10 → Bounds
  final : Fin 10 → Bounds

def endValue (s : Step) (i : Fin 10) : Dyadic :=
  s.A i 0+s.h*(s.A i 1+s.h*(s.A i 2+s.h*(s.A i 3+s.h*s.A i 4)))

def finalBox (s : Step) (r : Dyadic) (i : Fin 10) : Bounds :=
  ⟨endValue s i-r*s.w i,endValue s i+r*s.w i⟩

def tubeBox (s : Step) (path : Fin 10 → ℕ → Bounds) (i : Fin 10) : Bounds :=
  ⟨(path i 0).lo-s.rho*s.w i,(path i 0).hi+s.rho*s.w i⟩

def residualBound (s : Step) (i : Fin 10) (point along : ℕ → Bounds) : Dyadic :=
  gapD (s.A i 1) (point 0)+gapD (2*s.A i 2) (point 1)*s.h+gapD (3*s.A i 3) (point 2)*s.h^2+
    gapD (4*s.A i 4) (point 3)*s.h^3+4*gapD 0 (along 4)*s.h^4

def rowBound (s : Step) (D : Fin 10 → Fin 10 → ℕ → Bounds) (i : Fin 10) : Dyadic :=
  ∑ j, gapD 0 (D j i 1)*s.w j

def check (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (X : Fin 10 → Bounds) (s : Step) :
    Option Result := do
  require (decide (0 < s.h) && decide (0 ≤ s.rho) && decide (∀ i, 0 < s.w i))
  let start := run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 0) (boxD PT))
  let along := run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 s.h) (boxD PT))
  let point ← collect (components start)
  let box ← collect (components along)
  let path ← collect fun i => horner (ops prec 0) (s.A i) (timeD 0 s.h)
  let T := tubeBox s path
  let r ← radius (ops prec 0) (fun i => CheckedData.constant (spin i)) (fun i => boxD (T ⟨i,by omega⟩))
  require (decide (0 < (r 0).lo))
  let D ← collect fun j =>
    collect (components (run prec 1 spin (assemble (boxD PT) (fun k => lineD (T k) (unit j k)))))
  let e0 := maxOf fun i => divUp prec (gapD (s.A i 0) (X i)) (s.w i)
  let defect := maxOf fun i => divUp prec (residualBound s i (point i) (box i)) (s.w i)
  let K := maxOf fun i => divUp prec (rowBound s D i) (s.w i)
  require (decide (∀ i, gapD (s.A i 0) (X i) ≤ e0*s.w i) &&
    decide (∀ i, residualBound s i (point i) (box i) ≤ defect*s.w i) &&
    decide (∀ i, rowBound s D i ≤ K*s.w i) &&
    decide (0 ≤ e0) && decide (0 ≤ defect) && decide (0 ≤ K) &&
    decide (e0+s.h*(defect+K*s.rho) ≤ s.rho))
  -- Grönwall inside the tube: the end error is at most (e0+h*defect)/(1-h*K).
  let endR := divUp prec (e0+s.h*defect) (1-s.h*K)
  require (decide (s.h*K < 1) && decide (e0+s.h*defect ≤ endR*(1-s.h*K)))
  pure ⟨e0,defect,K,T,finalBox s endR⟩

/-! ### Soundness -/

section Soundness
noncomputable section
variable {N : ℕ}

def constantIn (b : Bounds) (c : ℝ) (hc : Contains b c) : CheckedFunction.Approx N s where
  fn := fun _ => c
  certificate := some {
    data := fun k => if k=0 then b else ⟨0,0⟩
    smooth := fun _ _ => contDiffAt_const
    encloses := by
      intro t _ k _
      by_cases hk : k=0
      · subst k; simpa using hc
      · simp [hk,Contains,coefficient,iteratedDeriv_const] }

def timeOn (s : Set ℝ) (lo hi : Dyadic) (hs : ∀ t ∈ s, t ∈ Icc lo.toReal hi.toReal) :
    CheckedFunction.Approx N s where
  fn := id
  certificate := some {
    data := fun k => if k=0 then ⟨lo,hi⟩ else if k=1 then ⟨1,1⟩ else ⟨0,0⟩
    smooth := fun _ _ => contDiffAt_id
    encloses := by
      intro t ht k _
      by_cases hk0 : k=0
      · subst k; simpa [Contains] using hs t ht
      · by_cases hk1 : k=1
        · subst k; simp [coefficient,Contains]
        · simp [hk0,hk1,Contains,coefficient,iteratedDeriv_id] }

theorem contains_of_erase {s : Set ℝ} (a : CheckedFunction.Approx N s) (d : ℕ → Bounds)
    (hd : CheckedData.erase a = some d) (t : ℝ) (ht : t ∈ s) : Contains (d 0) (a.fn t) := by
  unfold CheckedData.erase at hd
  cases hc : a.certificate with
  | none => simp [hc] at hd
  | some c =>
    simp only [hc,Option.map_some,Option.some.injEq] at hd
    subst hd
    simpa using c.encloses t ht 0 (Nat.zero_le N)

abbrev opA (prec N : ℕ) (s : Set ℝ) := CheckedFunction.operations (N := N) (RoundedProposals.proposals prec N) s

theorem fn_horner (prec : ℕ) (s : Set ℝ) (A : Fin 5 → Dyadic) (tA : CheckedFunction.Approx N s) (u : ℝ) :
    (horner (opA prec N s) A tA).fn u = horner realOperations A (tA.fn u) :=
  map_horner (CheckedFunction.operations_semantics _ s u) A tA

theorem erase_horner (prec : ℕ) (s : Set ℝ) (A : Fin 5 → Dyadic) (tA : CheckedFunction.Approx N s) :
    CheckedData.erase (horner (opA prec N s) A tA) = horner (ops prec N) A (CheckedData.erase tA) :=
  map_horner (CheckedData.operations_map _ s) A tA

theorem inputAt_assemble (s : Set ℝ) (ptA : CheckedFunction.Approx N s)
    (ys : Fin 10 → CheckedFunction.Approx N s) (u : ℝ) :
    CheckedFunction.inputAt (assemble ptA ys) u = full (ptA.fn u) (fun i => (ys i).fn u) := by
  simp only [CheckedFunction.inputAt,full,map_assemble]

theorem path_sound (prec : ℕ) (A : Fin 5 → Dyadic) (h : Dyadic) (c : ℕ → Bounds)
    (hc : horner (ops prec 0) A (timeD 0 h) = some c) (t : ℝ) (ht : t ∈ Icc 0 h.toReal) :
    Contains (c 0) (horner realOperations A t) := by
  let tA : CheckedFunction.Approx 0 (Icc 0 h.toReal) := timeOn _ 0 h (fun u hu => by simpa using hu)
  have he : CheckedData.erase (horner (opA prec 0 (Icc 0 h.toReal)) A tA) = some c := by
    rw [erase_horner]; exact hc
  simpa [fn_horner,tA,timeOn] using contains_of_erase _ c he t ht

theorem radius_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (B : Fin 3 → Bounds) (r : ℕ → Bounds)
    (hr : radius (ops prec 0) (fun i => CheckedData.constant (spin i)) (fun i => boxD (B i)) = some r)
    (hpos : 0 < (r 0).lo) (y : Fin 3 → ℝ) (hy : ∀ i, Contains (B i) (y i)) :
    0 < Cartesian.radius (CheckedFunction.spinValue spin) y := by
  let xs : Fin 3 → CheckedFunction.Approx 0 ({0}:Set ℝ) := fun i => constantIn (B i) (y i) (hy i)
  let as : Fin 3 → CheckedFunction.Approx 0 ({0}:Set ℝ) := fun i => CheckedFunction.constant _ (spin i)
  have he : CheckedData.erase (radius (opA prec 0 {0}) as xs) = some r := by
    rw [map_radius (CheckedData.operations_map _ _)]; exact hr
  have hv := contains_of_erase _ r he 0 rfl
  rw [map_radius (CheckedFunction.operations_semantics _ _ 0)] at hv
  have hreal : radius realOperations (fun i => (as i).fn 0) (fun i => (xs i).fn 0) =
      Cartesian.radius (CheckedFunction.spinValue spin) y := real_radius _ _
  rw [hreal] at hv
  exact (by simpa using Dyadic.toReal_lt_toReal.mpr hpos : (0:ℝ) < (r 0).lo.toReal).trans_le hv.1

theorem fderiv_component (a : Cartesian.Space) (pt : ℝ) (y : Reduced)
    (hr : 0 < Cartesian.radius a (full pt y).1) (v : Reduced) (i : Fin 10) :
    fderiv ℝ (fun z => field a pt z i) y v = fderiv ℝ (field a pt) y v i := by
  have hF := ((field_smooth a pt y hr).differentiableAt (by simp)).hasFDerivAt
  have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) i).hasFDerivAt.comp y hF
  rw [show (fun z => field a pt z i) = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℝ) i) ∘
    field a pt from rfl,hc.fderiv]
  rfl

theorem jacobian_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (T : Fin 10 → Bounds)
    (j : Fin 10) (D : Fin 10 → ℕ → Bounds)
    (hD : ∀ i, (run prec 1 spin (assemble (boxD PT) (fun k => lineD (T k) (unit j k)))).get
      (component i) = some (D i))
    (pt : ℝ) (hpt : Contains PT pt) (y : Reduced) (hy : ∀ k, Contains (T k) (y k))
    (hr : 0 < Cartesian.radius (CheckedFunction.spinValue spin) (full pt y).1) (i : Fin 10) :
    Contains (D i 1) (fderiv ℝ (field (CheckedFunction.spinValue spin) pt) y (Pi.single j 1) i) := by
  set a := CheckedFunction.spinValue spin
  let dir : Fin 10 → ℝ := fun k => if k=j then 1 else 0
  have hslope (k : Fin 10) : Contains (unit j k) (dir k) := by
    unfold unit; simp only [dir]; split_ifs <;> simp [Contains]
  let ys : Fin 10 → CheckedFunction.Approx 1 ({0}:Set ℝ) := fun k =>
    CheckedFunction.affineAtZero (y k) (dir k) (T k) (unit j k) (hy k) (hslope k)
  let inp := assemble (constantIn (N := 1) (s := ({0}:Set ℝ)) PT pt hpt) ys
  have hline (u : ℝ) : CheckedFunction.inputAt inp u = full pt (y+u • Pi.single j 1) := by
    rw [inputAt_assemble]
    congr 1
    funext k
    simp only [ys,CheckedFunction.affineAtZero,Pi.add_apply,Pi.smul_apply,smul_eq_mul,dir,
      Pi.single_apply]
  have hmap : KerrProgram.mapState CheckedData.erase inp =
      assemble (boxD PT) (fun k => lineD (T k) (unit j k)) := by
    simp only [inp,map_assemble]; rfl
  have hdata : (CheckedData.execute (RoundedProposals.proposals prec 1) 1 spin
      (KerrProgram.mapState CheckedData.erase inp)).get (component i) = some (D i) := by
    rw [hmap]; exact hD i
  have hpos : ContinuousAt (fun u => (CheckedFunction.inputAt inp u).1) 0 := by
    simp only [hline]
    exact ((full_smooth pt).continuous.comp (by fun_prop)).fst.continuousAt
  have hr0 : 0 < Cartesian.radius a (CheckedFunction.inputAt inp 0).1 := by simpa [hline] using hr
  have he := (CheckedData.rhs_enclosure _ _ spin inp (component i) (D i) hdata 0 rfl hpos hr0).2 1 le_rfl
  have hfield : CheckedData.field spin inp (component i) = fun u => field a pt (y+u • Pi.single j 1) i := by
    funext u; simp only [CheckedData.field,hline]; rfl
  rw [hfield,coefficient_direction_first (fun z => field a pt z i) y (Pi.single j 1)
    (differentiableAt_pi.mp ((field_smooth a pt y hr).differentiableAt (by simp)) i)] at he
  rwa [fderiv_component a pt y hr] at he

theorem poly_continuous (A : Fin 10 → Fin 5 → Dyadic) : Continuous (poly A) := by
  unfold poly; fun_prop

theorem inputAt_step (prec : ℕ) (s : Set ℝ) (A : Fin 10 → Fin 5 → Dyadic) (lo hi : Dyadic)
    (hs : ∀ t ∈ s, t ∈ Icc lo.toReal hi.toReal) (PT : Bounds) (pt : ℝ) (hpt : Contains PT pt) (u : ℝ) :
    CheckedFunction.inputAt (stepInput (opA prec N s) A (timeOn s lo hi hs) (constantIn PT pt hpt)) u =
      full pt (poly A u) := by
  simp only [stepInput,inputAt_assemble,fn_horner]
  rfl

theorem erase_step (prec : ℕ) (s : Set ℝ) (A : Fin 10 → Fin 5 → Dyadic) (lo hi : Dyadic)
    (hs : ∀ t ∈ s, t ∈ Icc lo.toReal hi.toReal) (PT : Bounds) (pt : ℝ) (hpt : Contains PT pt) :
    KerrProgram.mapState CheckedData.erase
      (stepInput (opA prec N s) A (timeOn s lo hi hs) (constantIn PT pt hpt)) =
      stepInput (ops prec N) A (timeD lo hi) (boxD PT) := by
  simp only [stepInput,map_assemble,erase_horner]
  rfl

theorem residual_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (s : Step) (hh : 0 < s.h.toReal)
    (point box : Fin 10 → ℕ → Bounds)
    (hpoint : ∀ i, (run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 0) (boxD PT))).get
      (component i) = some (point i))
    (hbox : ∀ i, (run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 s.h) (boxD PT))).get
      (component i) = some (box i))
    (pt : ℝ) (hpt : Contains PT pt)
    (hdom : ∀ t ∈ Icc 0 s.h.toReal,
      0 < Cartesian.radius (CheckedFunction.spinValue spin) (full pt (poly s.A t)).1)
    (t : ℝ) (ht : t ∈ Icc 0 s.h.toReal) (i : Fin 10) :
    |field (CheckedFunction.spinValue spin) pt (poly s.A t) i-polyDeriv s.A t i| ≤
      (residualBound s i (point i) (box i)).toReal := by
  have h0 : ∀ u ∈ ({0}:Set ℝ), u ∈ Icc (0:Dyadic).toReal (0:Dyadic).toReal := by simp
  have hI : ∀ u ∈ Icc 0 s.h.toReal, u ∈ Icc (0:Dyadic).toReal s.h.toReal := by simp
  let start := stepInput (opA prec 4 {0}) s.A (timeOn {0} 0 0 h0) (constantIn PT pt hpt)
  let step := stepInput (opA prec 4 (Icc 0 s.h.toReal)) s.A (timeOn _ 0 s.h hI) (constantIn PT pt hpt)
  have hstart := inputAt_step (N := 4) prec {0} s.A 0 0 h0 PT pt hpt
  have hstep := inputAt_step (N := 4) prec (Icc 0 s.h.toReal) s.A 0 s.h hI PT pt hpt
  have hsame : CheckedFunction.inputAt start = CheckedFunction.inputAt step := by
    funext u; rw [hstart,hstep]
  have hp : (CheckedData.execute (RoundedProposals.proposals prec 4) 4 spin
      (KerrProgram.mapState CheckedData.erase start)).get (component i) = some (point i) := by
    rw [erase_step]; exact hpoint i
  have hb : (CheckedData.execute (RoundedProposals.proposals prec 4) 4 spin
      (KerrProgram.mapState CheckedData.erase step)).get (component i) = some (box i) := by
    rw [erase_step]; exact hbox i
  have hpos (u : ℝ) (_ : u ∈ Icc 0 s.h.toReal) :
      ContinuousAt (fun v => (CheckedFunction.inputAt step v).1) u := by
    have hf : (fun v => (CheckedFunction.inputAt step v).1) = fun v => (full pt (poly s.A v)).1 :=
      funext fun v => by rw [hstep]
    rw [hf]
    exact ((full_smooth pt).continuous.comp (poly_continuous s.A)).fst.continuousAt
  have hr (u : ℝ) (hu : u ∈ Icc 0 s.h.toReal) :
      0 < Cartesian.radius (CheckedFunction.spinValue spin) (CheckedFunction.inputAt step u).1 := by
    rw [hstep]; exact hdom u hu
  have key := CheckedData.kerr_residual (RoundedProposals.proposals prec 4) spin _ hh {0} rfl start step
    hsame (component i) (point i) (box i) hp hb hpos hr
    (fun k : Fin 4 => (((k:ℕ):ℝ)+1)*(s.A i k.succ).toReal) t ht
  have hfield : CheckedData.field spin step (component i) t =
      field (CheckedFunction.spinValue spin) pt (poly s.A t) i := by
    simp only [CheckedData.field]; rw [hstep]; rfl
  rw [hfield] at key
  rw [abs_sub_comm]
  refine key.trans (le_of_eq ?_)
  simp only [residualBound,Fin.sum_univ_four,Dyadic.toReal_add,Dyadic.toReal_mul,Dyadic.toReal_pow,
    toReal_gapD,real_zero]
  norm_num [Dyadic.toReal_ofNat]

theorem toReal_rowBound (s : Step) (D : Fin 10 → Fin 10 → ℕ → Bounds) (i : Fin 10) :
    (rowBound s D i).toReal = ∑ j, (gapD 0 (D j i 1)).toReal*(s.w j).toReal := by
  unfold rowBound
  rw [show (∑ j, gapD 0 (D j i 1)*s.w j).toReal =
    Dyadic.toRealAddMonoidHom (∑ j, gapD 0 (D j i 1)*s.w j) from rfl,map_sum]
  simp [Dyadic.toRealAddMonoidHom,Dyadic.toReal_mul]

theorem endValue_real (s : Step) (i : Fin 10) : (endValue s i).toReal = poly s.A s.h.toReal i := by
  simp [endValue,poly,Dyadic.toReal_add,Dyadic.toReal_mul]

theorem near_contains {b : Bounds} {p y r : ℝ} (hp : Contains b p) (hy : |y-p| ≤ r) :
    y ∈ Icc (b.lo.toReal-r) (b.hi.toReal+r) := by
  obtain ⟨h1,h2⟩ := abs_le.mp hy
  exact ⟨by linarith [hp.1],by linarith [hp.2]⟩

theorem tube_contains (s : Step) (path : Fin 10 → ℕ → Bounds) (i : Fin 10) {p y : ℝ}
    (hp : Contains (path i 0) p) (hy : |y-p| ≤ s.rho.toReal*(s.w i).toReal) :
    Contains (tubeBox s path i) y := by
  simpa [Contains,tubeBox,toReal_sub,Dyadic.toReal_add,Dyadic.toReal_mul] using near_contains hp hy

theorem gronwall_le (e0 K δ x : ℝ) (he0 : 0 ≤ e0) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hKx : K*x < 1) : gronwallBound e0 K δ x ≤ (e0+x*δ)/(1-K*x) := by
  have hd : 0 < 1-K*x := by linarith
  rcases hK.eq_or_lt with h0 | hpos
  · subst h0
    simp [gronwallBound_K0,mul_comm]
  · rw [gronwallBound_of_K_ne_0 hpos.ne',le_div_iff₀ hd]
    set z := K*x
    have hexp : Real.exp z*(1-z) ≤ 1 := by
      have h1 := Real.add_one_le_exp (-z)
      have h2 : Real.exp z*Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos z]
    have hterm : δ/K*(Real.exp z-1)*(1-z) ≤ x*δ := by
      have : (Real.exp z-1)*(1-z) ≤ z := by nlinarith
      calc δ/K*(Real.exp z-1)*(1-z) = δ/K*((Real.exp z-1)*(1-z)) := by ring
        _ ≤ δ/K*z := mul_le_mul_of_nonneg_left this (div_nonneg hδ hpos.le)
        _ = x*δ := by simp only [z]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hexp he0]

theorem dyadic_le {a b : Dyadic} (h : a ≤ b) : a.toReal ≤ b.toReal := Dyadic.toReal_le_toReal.mpr h

/-- A successful check yields an exact solution of the reduced Kerr system
for every time momentum and initial point in the input boxes. It stays in
the reported tube over the whole step and ends in the reported box. -/
theorem check_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (X : Fin 10 → Bounds)
    (s : Step) (res : Result) (hc : check prec spin PT X s = some res)
    (pt : ℝ) (hpt : Contains PT pt) (x : Reduced) (hx : ∀ i, Contains (X i) (x i)) :
    ∃ y : ℝ → Reduced, y 0 = x ∧
      (∀ t ∈ Icc 0 s.h.toReal, HasDerivWithinAt y
        (field (CheckedFunction.spinValue spin) pt (y t)) (Icc 0 s.h.toReal) t) ∧
      (∀ t ∈ Icc 0 s.h.toReal, ∀ i, Contains (res.tube i) (y t i)) ∧
      (∀ t ∈ Icc 0 s.h.toReal, 0 < Cartesian.radius (CheckedFunction.spinValue spin) (full pt (y t)).1) ∧
      ∀ i, Contains (res.final i) (y s.h.toReal i) := by
  simp only [check,bind,Option.bind_eq_some_iff,pure] at hc
  obtain ⟨u1,h1,point,hpoint,box,hbox,path,hpath,r,hr,u2,h2,D,hD,u3,h3,u4,h4,hres⟩ := hc
  have b1 := require_some h1
  have b2 := require_some h2
  have b3 := require_some h3
  have b4 := require_some h4
  simp only [Bool.and_eq_true,decide_eq_true_eq] at b1 b2 b3 b4
  obtain ⟨⟨hh,hρ⟩,hw⟩ := b1
  obtain ⟨⟨⟨⟨⟨⟨he,hδ⟩,hK⟩,he0⟩,hδ0⟩,hK0⟩,hinc⟩ := b3
  cases hres
  set a := CheckedFunction.spinValue spin
  set e0 := maxOf fun i => divUp prec (gapD (s.A i 0) (X i)) (s.w i)
  set δ := maxOf fun i => divUp prec (residualBound s i (point i) (box i)) (s.w i)
  set K := maxOf fun i => divUp prec (rowBound s D i) (s.w i)
  set T := tubeBox s path
  have hwr (i : Fin 10) : 0 < (s.w i).toReal := by simpa using Dyadic.toReal_lt_toReal.mpr (hw i)
  have hhr : 0 < s.h.toReal := by simpa using Dyadic.toReal_lt_toReal.mpr hh
  have hρr : 0 ≤ s.rho.toReal := by simpa using dyadic_le hρ
  have hpathc (t : ℝ) (ht : t ∈ Icc 0 s.h.toReal) (i : Fin 10) : Contains (path i 0) (poly s.A t i) :=
    path_sound prec (s.A i) s.h (path i) (collect_some hpath i) t ht
  have hinT (t : ℝ) (ht : t ∈ Icc 0 s.h.toReal) (y : Reduced)
      (hy : ∀ i, |y i-poly s.A t i| ≤ s.rho.toReal*(s.w i).toReal) (i : Fin 10) : Contains (T i) (y i) :=
    tube_contains s path i (hpathc t ht i) (hy i)
  have hdomain (t : ℝ) (ht : t ∈ Icc 0 s.h.toReal) (y : Reduced)
      (hy : ∀ i, |y i-poly s.A t i| ≤ s.rho.toReal*(s.w i).toReal) : 0 < Cartesian.radius a (full pt y).1 :=
    radius_sound prec spin (fun i => T ⟨i,by omega⟩) r hr b2 (full pt y).1
      (fun i => hinT t ht y hy ⟨i,by omega⟩)
  obtain ⟨y,hy0,hyd,hyb,hyg⟩ := certified_step a pt (fun i => (s.w i).toReal) hwr s.h.toReal hhr.le
    (poly s.A) (polyDeriv s.A) (fun t _ => (poly_hasDerivAt s.A t).hasDerivWithinAt)
    (polyDeriv_continuous s.A).continuousOn
    s.rho.toReal e0.toReal δ.toReal K.toReal hρr (by simpa using dyadic_le he0)
    (by simpa using dyadic_le hδ0) (by simpa using dyadic_le hK0) hdomain
    (by
      intro t ht z hz i
      have hr0 := hdomain t ht z hz
      calc ∑ j, |fderiv ℝ (field a pt) z (Pi.single j 1) i| * (s.w j).toReal
          ≤ ∑ j, (gapD 0 (D j i 1)).toReal*(s.w j).toReal := by
            refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hwr j).le
            have hc := jacobian_sound prec spin PT T j (D j) (fun i => collect_some (collect_some hD j) i)
              pt hpt z (hinT t ht z hz) hr0 i
            simpa [toReal_gapD] using CheckedData.gap_sound (a := 0) hc
        _ = (rowBound s D i).toReal := (toReal_rowBound s D i).symm
        _ ≤ K.toReal*(s.w i).toReal := by simpa [Dyadic.toReal_mul] using dyadic_le (hK i))
    (by
      intro t ht i
      refine (residual_sound prec spin PT s hhr point box (fun i => collect_some hpoint i)
        (fun i => collect_some hbox i) pt hpt
        (fun u hu => hdomain u hu _ (fun k => by simpa using mul_nonneg hρr (hwr k).le)) t ht i).trans ?_
      simpa [Dyadic.toReal_mul] using dyadic_le (hδ i))
    x
    (by
      intro i
      have hg := CheckedData.gap_sound (a := (s.A i 0).toReal) (hx i)
      rw [← toReal_gapD] at hg
      have hp0 : poly s.A 0 i = (s.A i 0).toReal := by simp [poly]
      rw [hp0,abs_sub_comm]
      exact hg.trans (by simpa [Dyadic.toReal_mul] using dyadic_le (he i)))
    (by simpa [Dyadic.toReal_add,Dyadic.toReal_mul] using dyadic_le hinc)
  refine ⟨y,hy0,hyd,fun t ht i => hinT t ht (y t) (hyb t ht) i,
    fun t ht => hdomain t ht (y t) (hyb t ht),fun i => ?_⟩
  set endR := divUp prec (e0+s.h*δ) (1-s.h*K)
  obtain ⟨hKh,hR⟩ := b4
  have hKhr : K.toReal*s.h.toReal < 1 := by
    have := Dyadic.toReal_lt_toReal.mpr hKh; simp [Dyadic.toReal_mul] at this; linarith
  have hRr : e0.toReal+s.h.toReal*δ.toReal ≤ endR.toReal*(1-K.toReal*s.h.toReal) := by
    have := dyadic_le hR
    simp only [Dyadic.toReal_add,Dyadic.toReal_mul,toReal_sub,real_one] at this
    linarith
  have hgb := gronwall_le e0.toReal K.toReal δ.toReal s.h.toReal (by simpa using dyadic_le he0)
    (by simpa using dyadic_le hδ0) (by simpa using dyadic_le hK0) hKhr
  have hbound : gronwallBound e0.toReal K.toReal δ.toReal s.h.toReal ≤ endR.toReal := by
    refine hgb.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hyi := (hyg s.h.toReal ⟨hhr.le,le_rfl⟩ i).trans
    (mul_le_mul_of_nonneg_right hbound (hwr i).le)
  have hend := near_contains (b := ⟨endValue s i,endValue s i⟩) (p := poly s.A s.h.toReal i)
    (by simp [Contains,endValue_real]) hyi
  simpa [Contains,finalBox,toReal_sub,Dyadic.toReal_add,Dyadic.toReal_mul] using hend

end

end Soundness

end BlackHole.StepCheck
