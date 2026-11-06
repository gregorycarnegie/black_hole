module
public import BlackHole.TraceCheck

/-! Capture and escape classification. A step is classified only when the
event enclosures over its whole tube and its end box are strictly separated
from the boundaries (horizon clearance 1/500, radius 1600). Ambiguous steps
leave the ray unresolved. `trace_sound` states the resulting facts about
every exact ray that starts in the initial boxes. -/

@[expose] public section
open Set
namespace BlackHole.RayEvents
open DyadicInterval KerrProgram StepField StepCheck TraceCheck

/-! ### Programs evaluated over boxes -/

def clearanceP (spin : Fin 3 → Dyadic) {S : Type} (op : Operations S) (x : Fin 3 → S) : S :=
  let a : Fin 3 → S := fun i => op.constant (spin i)
  op.sub (radius op a x) (op.add (op.constant 1) (op.sqrt (op.sub (op.constant 1) (dot3 op a a))))

def normSqP {S : Type} (op : Operations S) (x : Fin 3 → S) : S := dot3 op x x

noncomputable section

def horizon (a : Cartesian.Space) : ℝ := 1+Real.sqrt (1-dotProduct a a)
def clearance (a x : Cartesian.Space) : ℝ := Cartesian.radius a x-horizon a

theorem real_clearance (spin : Fin 3 → Dyadic) (x : Cartesian.Space) :
    clearanceP spin realOperations x = clearance (CheckedFunction.spinValue spin) x := by
  simp only [clearanceP,clearance,horizon]
  rw [real_radius,real_dot3]
  simp [realOperations]
  rfl

theorem real_normSq (x : Cartesian.Space) : normSqP realOperations x = dotProduct x x := real_dot3 x x

/-- A natural program evaluated on boxes encloses its real value at every point. -/
theorem box_sound {m : ℕ} (prec : ℕ) (prog : ∀ {S : Type}, Operations S → (Fin m → S) → S)
    (hnat : ∀ {S T : Type} (op : Operations S) (target : Operations T) (eval : S → T),
      OperationMap op target eval → ∀ v, eval (prog op v) = prog target (fun i => eval (v i)))
    (B : Fin m → Bounds) (d : ℕ → Bounds) (hd : prog (ops prec 0) (fun i => boxD (B i)) = some d)
    (v : Fin m → ℝ) (hv : ∀ i, Contains (B i) (v i)) : Contains (d 0) (prog realOperations v) := by
  let xs : Fin m → CheckedFunction.Approx 0 ({0}:Set ℝ) := fun i => constantIn (B i) (v i) (hv i)
  have he : CheckedData.erase (prog (opA prec 0 {0}) xs) = some d := by
    rw [hnat _ _ _ (CheckedData.operations_map _ _)]; exact hd
  have hc := contains_of_erase _ d he 0 rfl
  rwa [hnat _ _ _ (CheckedFunction.operations_semantics _ _ 0)] at hc

theorem clearance_nat (spin : Fin 3 → Dyadic) {S T : Type} (op : Operations S) (target : Operations T)
    (eval : S → T) (h : OperationMap op target eval) (v : Fin 3 → S) :
    eval (clearanceP spin op v) = clearanceP spin target (fun i => eval (v i)) := by
  simp [clearanceP,map_radius h,dot3,map_sum3 h,h.sub,h.add,h.sqrt,h.constant,h.mul]

theorem normSq_nat {S T : Type} (op : Operations S) (target : Operations T)
    (eval : S → T) (h : OperationMap op target eval) (v : Fin 3 → S) :
    eval (normSqP op v) = normSqP target (fun i => eval (v i)) := by
  simp [normSqP,dot3,map_sum3 h,h.mul]

end

/-! ### Verdicts -/

inductive Verdict where
  | running
  | captured
  | escaped
  deriving DecidableEq, Repr

def positionBox (B : Fin 10 → Bounds) (i : Fin 3) : Bounds := B ⟨i,by omega⟩

/-- Exact dyadic comparisons with 1/500 and 1600². -/
def clearAbove (b : Bounds) : Bool := decide (1 < 500*b.lo)
def clearBelow (b : Bounds) : Bool := decide (500*b.hi < 1)
def inside (b : Bounds) : Bool := decide (b.hi < 1600*1600)
def outside (b : Bounds) : Bool := decide (1600*1600 < b.lo)

def verdict (prec : ℕ) (spin : Fin 3 → Dyadic) (r : Result) : Option Verdict := do
  let tc ← clearanceP spin (ops prec 0) (fun i => boxD (positionBox r.tube i))
  let tr ← normSqP (ops prec 0) (fun i => boxD (positionBox r.tube i))
  let ec ← clearanceP spin (ops prec 0) (fun i => boxD (positionBox r.final i))
  let er ← normSqP (ops prec 0) (fun i => boxD (positionBox r.final i))
  if clearAbove (tc 0) && inside (tr 0) then some .running
  else if clearBelow (ec 0) && inside (tr 0) then some .captured
  else if outside (er 0) && clearAbove (tc 0) then some .escaped
  else none

/-- Every step but the last must be event-free; the last decides the verdict. -/
def checkTrace (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) :
    (Fin 10 → Bounds) → List Step → Option (List Result × Verdict)
  | _, [] => none
  | X, [s] => do
    let r ← check prec spin PT X s
    let v ← verdict prec spin r
    pure ([r],v)
  | X, s :: s' :: rest => do
    let r ← check prec spin PT X s
    let v ← verdict prec spin r
    require (v == .running)
    let out ← checkTrace prec spin PT r.final (s' :: rest)
    pure (r :: out.1,out.2)

/-! ### Semantics -/

noncomputable section

def position (pt : ℝ) (y : Reduced) : Cartesian.Space := (full pt y).1

/-- Facts every point of the trace satisfies, given the final verdict. -/
def Throughout (a : Cartesian.Space) (pt : ℝ) (y : Reduced) : Verdict → Prop
  | .running => 1/500 < clearance a (position pt y) ∧ dotProduct (position pt y) (position pt y) < 1600^2
  | .captured => dotProduct (position pt y) (position pt y) < 1600^2
  | .escaped => 1/500 < clearance a (position pt y)

/-- The event reached at the end of the trace. -/
def AtEnd (a : Cartesian.Space) (pt : ℝ) (y : Reduced) : Verdict → Prop
  | .running => True
  | .captured => clearance a (position pt y) < 1/500
  | .escaped => 1600^2 < dotProduct (position pt y) (position pt y)

theorem throughout_of_running {a : Cartesian.Space} {pt : ℝ} {y : Reduced} (v : Verdict)
    (h : Throughout a pt y .running) : Throughout a pt y v := by
  cases v
  · exact h
  · exact h.2
  · exact h.1

theorem position_contains {B : Fin 10 → Bounds} {pt : ℝ} {y : Reduced} (h : ∀ i, Contains (B i) (y i))
    (i : Fin 3) : Contains (positionBox B i) (position pt y i) := h ⟨i,by omega⟩

theorem clearance_box (prec : ℕ) (spin : Fin 3 → Dyadic) (B : Fin 10 → Bounds) (d : ℕ → Bounds)
    (hd : clearanceP spin (ops prec 0) (fun i => boxD (positionBox B i)) = some d)
    (pt : ℝ) (y : Reduced) (hy : ∀ i, Contains (B i) (y i)) :
    Contains (d 0) (clearance (CheckedFunction.spinValue spin) (position pt y)) := by
  rw [← real_clearance]
  exact box_sound prec (clearanceP spin) (clearance_nat spin) _ d hd _ (position_contains hy)

theorem normSq_box (prec : ℕ) (B : Fin 10 → Bounds) (d : ℕ → Bounds)
    (hd : normSqP (ops prec 0) (fun i => boxD (positionBox B i)) = some d)
    (pt : ℝ) (y : Reduced) (hy : ∀ i, Contains (B i) (y i)) :
    Contains (d 0) (dotProduct (position pt y) (position pt y)) := by
  rw [← real_normSq]
  exact box_sound prec normSqP normSq_nat _ d hd _ (position_contains hy)

theorem above_sound {b : Bounds} {x : ℝ} (h : clearAbove b = true) (hx : Contains b x) : 1/500 < x := by
  have h' := Dyadic.toReal_lt_toReal.mpr (of_decide_eq_true h)
  simp [Dyadic.toReal_mul] at h'
  have := hx.1
  linarith

theorem below_sound {b : Bounds} {x : ℝ} (h : clearBelow b = true) (hx : Contains b x) : x < 1/500 := by
  have h' := Dyadic.toReal_lt_toReal.mpr (of_decide_eq_true h)
  simp [Dyadic.toReal_mul] at h'
  have := hx.2
  linarith

theorem inside_sound {b : Bounds} {x : ℝ} (h : inside b = true) (hx : Contains b x) : x < 1600^2 := by
  have h' := Dyadic.toReal_lt_toReal.mpr (of_decide_eq_true h)
  simp [Dyadic.toReal_mul] at h'
  have := hx.2
  nlinarith

theorem outside_sound {b : Bounds} {x : ℝ} (h : outside b = true) (hx : Contains b x) : 1600^2 < x := by
  have h' := Dyadic.toReal_lt_toReal.mpr (of_decide_eq_true h)
  simp [Dyadic.toReal_mul] at h'
  have := hx.1
  nlinarith

/-- A step verdict holds along the whole step for any curve in its tube. -/
theorem verdict_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (r : Result) (v : Verdict)
    (hv : verdict prec spin r = some v) (pt : ℝ) (z : ℝ → Reduced) (t0 h : ℝ)
    (htube : ∀ t ∈ Icc t0 (t0+h), ∀ i, Contains (r.tube i) (z t i))
    (hfinal : ∀ i, Contains (r.final i) (z (t0+h) i)) :
    (∀ t ∈ Icc t0 (t0+h), Throughout (CheckedFunction.spinValue spin) pt (z t) v) ∧
      AtEnd (CheckedFunction.spinValue spin) pt (z (t0+h)) v := by
  simp only [verdict,bind,Option.bind_eq_some_iff] at hv
  obtain ⟨tc,htc,tr,htr,ec,hec,er,her,hv⟩ := hv
  have hTc (t : ℝ) (ht : t ∈ Icc t0 (t0+h)) := clearance_box prec spin r.tube tc htc pt (z t) (htube t ht)
  have hTr (t : ℝ) (ht : t ∈ Icc t0 (t0+h)) := normSq_box prec r.tube tr htr pt (z t) (htube t ht)
  have hEc := clearance_box prec spin r.final ec hec pt (z (t0+h)) hfinal
  have hEr := normSq_box prec r.final er her pt (z (t0+h)) hfinal
  split_ifs at hv with h1 h2 h3 <;> simp only [Option.some.injEq] at hv <;> subst hv
  · simp only [Bool.and_eq_true] at h1
    exact ⟨fun t ht => ⟨above_sound h1.1 (hTc t ht),inside_sound h1.2 (hTr t ht)⟩,trivial⟩
  · simp only [Bool.and_eq_true] at h2
    exact ⟨fun t ht => inside_sound h2.2 (hTr t ht),below_sound h2.1 hEc⟩
  · simp only [Bool.and_eq_true] at h3
    exact ⟨fun t ht => above_sound h3.2 (hTc t ht),outside_sound h3.1 hEr⟩

theorem checkTrace_steps (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (out : List Result × Verdict),
      checkTrace prec spin PT X steps = some out → checkSteps prec spin PT X steps = some out.1
  | _,[],out,h => by simp [checkTrace] at h
  | X,[s],out,h => by
    simp only [checkTrace,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
    obtain ⟨r,hr,v,hv,rfl⟩ := h
    simp [checkSteps,hr]
  | X,s :: s' :: rest,out,h => by
    simp only [checkTrace,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
    obtain ⟨r,hr,v,hv,u,hu,out',hout',rfl⟩ := h
    have := checkTrace_steps prec spin PT r.final (s' :: rest) out' hout'
    simp only [checkSteps,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at this ⊢
    exact ⟨r,hr,out'.1,by simpa [checkSteps] using this,rfl⟩

/-- Every exact solution that starts in the initial boxes and stays where the
Kerr equations are defined satisfies the verdict's facts over the whole trace. -/
theorem trace_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (pt : ℝ) (hpt : Contains PT pt) :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (out : List Result × Verdict),
      checkTrace prec spin PT X steps = some out →
      ∀ z : ℝ → Reduced, (∀ i, Contains (X i) (z 0 i)) →
        Solves (CheckedFunction.spinValue spin) pt z (duration steps) →
        InDomain (CheckedFunction.spinValue spin) pt z (duration steps) →
        (∀ t ∈ Icc 0 (duration steps), Throughout (CheckedFunction.spinValue spin) pt (z t) out.2) ∧
          AtEnd (CheckedFunction.spinValue spin) pt (z (duration steps)) out.2
  | _,[],out,h,_,_,_,_ => by simp [checkTrace] at h
  | X,[s],out,h,z,hz0,hz,hzU => by
    simp only [checkTrace,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
    obtain ⟨r,hr,v,hv,rfl⟩ := h
    have hrs : checkSteps prec spin PT X [s] = some [r] := by
      simp [checkSteps,hr]
    have hF := steps_unique prec spin PT pt hpt X [s] [r] hrs z hz0 hz hzU
    simp only [Follows,zero_add] at hF
    have hd : duration [s] = s.h.toReal := by simp [duration]
    rw [hd]
    have := verdict_sound prec spin r v hv pt z 0 s.h.toReal
      (fun t ht i => (hF.1 t (by simpa using ht)).1 i) (fun i => by simpa using hF.2.1 i)
    simpa using this
  | X,s :: s' :: rest,out,h,z,hz0,hz,hzU => by
    simp only [checkTrace,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
    obtain ⟨r,hr,v,hv,u,hu,out',hout',rfl⟩ := h
    have hrun : v = .running := by simpa using require_some hu
    subst hrun
    have hh := check_positive hr
    have hrest0 : 0 ≤ duration (s' :: rest) :=
      duration_nonneg r.final (s' :: rest) out'.1 (checkTrace_steps prec spin PT _ _ out' hout')
    have hD : duration (s :: s' :: rest) = s.h.toReal+duration (s' :: rest) := rfl
    rw [hD] at hz hzU ⊢
    obtain ⟨y,hy0,hyd,hyT,hyU,hyF⟩ := check_sound prec spin PT X s r hr pt hpt (z 0) hz0
    have hsub : Icc 0 s.h.toReal ⊆ Icc 0 (s.h.toReal+duration (s' :: rest)) :=
      Icc_subset_Icc le_rfl (by linarith)
    have heq := solution_unique _ pt s.h.toReal y z hyd
      (fun t ht => (hz t (hsub ht)).mono hsub) hyU (fun t ht => hzU t (hsub ht)) hy0
    have hend : z s.h.toReal = y s.h.toReal := (heq ⟨hh.le,le_rfl⟩).symm
    have hfirst := verdict_sound prec spin r .running hv pt z 0 s.h.toReal
      (fun t ht i => by rw [← heq (by simpa using ht)]; exact hyT t (by simpa using ht) i)
      (fun i => by simpa [hend] using hyF i)
    have hrec := trace_sound prec spin PT pt hpt r.final (s' :: rest) out' hout'
      (fun t => z (t+s.h.toReal)) (fun i => by simpa [hend] using hyF i)
      (solves_shift _ pt z _ _ hh.le hz)
      (fun t ht => hzU (t+s.h.toReal) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    refine ⟨fun t ht => ?_,?_⟩
    · by_cases hts : t ≤ s.h.toReal
      · exact throughout_of_running _ (hfirst.1 t ⟨ht.1,by simpa using hts⟩)
      · have := hrec.1 (t-s.h.toReal) ⟨by linarith,by linarith [ht.2]⟩
        simpa using this
    · have := hrec.2
      simpa [add_comm] using this

end

end BlackHole.RayEvents
