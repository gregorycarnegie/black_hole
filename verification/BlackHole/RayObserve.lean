module
public import BlackHole.RayEvents
public import BlackHole.DirectionError

/-! Camera initial data and escaping observables. The camera state is the
real value of `cameraY`/`cameraPt` (a past null ray with Eulerian energy one
and a transverse unit screen, following `src/certified/camera.rs`); checked
evaluation encloses it. At an escape, the static-observer redshift, output
direction, screen norm and transversality are bounded against the targets. -/

@[expose] public section
open Set
namespace BlackHole.RayObserve
open DyadicInterval KerrProgram StepField StepCheck TraceCheck RayEvents

/-! ### Camera -/

section Camera
variable (spin pos dir hint : Fin 3 → Dyadic) {S : Type} (op : Operations S)

def cameraMomentum : Fin 4 → S :=
  let c := op.constant
  let a : Fin 3 → S := fun i => c (spin i)
  let x : Fin 3 → S := fun i => c (pos i)
  let m := geometry op a x
  let sdot := fun (u v : Fin 3 → S) =>
    sum3 op (fun i => sum3 op (fun j => op.mul (op.mul (u i) (m.metric i.succ j.succ)) (v j)))
  let d0 : Fin 3 → S := fun i => c (dir i)
  let dn := op.sqrt (sdot d0 d0)
  let d : Fin 3 → S := fun i => op.div (d0 i) dn
  let alpha := op.div (c 1) (op.sqrt (op.neg (m.inverse 0 0)))
  let k : Fin 4 → S :=
    Fin.cases (op.neg (op.div (c 1) alpha)) (fun i => op.add (op.mul alpha (m.inverse 0 i.succ)) (d i))
  fun i => sum4 op (fun j => op.mul (m.metric i j) (k j))

def cameraScreen : Fin 3 → S :=
  let c := op.constant
  let a : Fin 3 → S := fun i => c (spin i)
  let x : Fin 3 → S := fun i => c (pos i)
  let m := geometry op a x
  let sdot := fun (u v : Fin 3 → S) =>
    sum3 op (fun i => sum3 op (fun j => op.mul (op.mul (u i) (m.metric i.succ j.succ)) (v j)))
  let d0 : Fin 3 → S := fun i => c (dir i)
  let dn := op.sqrt (sdot d0 d0)
  let d : Fin 3 → S := fun i => op.div (d0 i) dn
  let h0 : Fin 3 → S := fun i => c (hint i)
  let proj := sdot h0 d
  let s0 : Fin 3 → S := fun i => op.sub (h0 i) (op.mul proj (d i))
  let sn := op.sqrt (sdot s0 s0)
  fun i => op.div (s0 i) sn

def cameraPt : S := cameraMomentum spin pos dir op 0

def cameraY : Fin 10 → S := fun i =>
  if h : i.val < 3 then op.constant (pos ⟨i,h⟩)
  else if h' : i.val < 6 then cameraMomentum spin pos dir op ⟨i-2,by omega⟩
  else if h'' : i.val = 6 then op.constant 0
  else cameraScreen spin pos dir hint op ⟨i-7,by omega⟩

end Camera

theorem map_geometry_metric {S T : Type} {op : Operations S} {target : Operations T} {eval : S → T}
    (h : OperationMap op target eval) (a x : Fin 3 → S) (i j : Fin 4) :
    eval ((geometry op a x).metric i j) =
      (geometry target (fun k => eval (a k)) (fun k => eval (x k))).metric i j :=
  congrArg (fun g => g.metric i j) (map_geometry h a x)

theorem map_geometry_inverse {S T : Type} {op : Operations S} {target : Operations T} {eval : S → T}
    (h : OperationMap op target eval) (a x : Fin 3 → S) (i j : Fin 4) :
    eval ((geometry op a x).inverse i j) =
      (geometry target (fun k => eval (a k)) (fun k => eval (x k))).inverse i j :=
  congrArg (fun g => g.inverse i j) (map_geometry h a x)

theorem cameraMomentum_nat (spin pos dir : Fin 3 → Dyadic) {S T : Type} (op : Operations S)
    (target : Operations T) (eval : S → T) (h : OperationMap op target eval) (i : Fin 4) :
    eval (cameraMomentum spin pos dir op i) = cameraMomentum spin pos dir target i := by
  simp only [cameraMomentum,map_sum4 h,map_sum3 h,h.mul,h.add,h.div,h.sqrt,h.neg,h.constant,
    map_geometry_metric h,map_geometry_inverse h,map_cases]

theorem cameraScreen_nat (spin pos dir hint : Fin 3 → Dyadic) {S T : Type} (op : Operations S)
    (target : Operations T) (eval : S → T) (h : OperationMap op target eval) (i : Fin 3) :
    eval (cameraScreen spin pos dir hint op i) = cameraScreen spin pos dir hint target i := by
  simp only [cameraScreen,map_sum3 h,h.mul,h.sub,h.div,h.sqrt,h.constant,map_geometry_metric h]

theorem cameraY_nat (spin pos dir hint : Fin 3 → Dyadic) {S T : Type} (op : Operations S)
    (target : Operations T) (eval : S → T) (h : OperationMap op target eval) (i : Fin 10) :
    eval (cameraY spin pos dir hint op i) = cameraY spin pos dir hint target i := by
  unfold cameraY
  split_ifs
  · exact h.constant _
  · exact cameraMomentum_nat spin pos dir op target eval h _
  · exact h.constant _
  · exact cameraScreen_nat spin pos dir hint op target eval h _

/-- A natural constant program evaluated by the checker encloses its real value. -/
theorem constant_sound (prec : ℕ) (prog : ∀ {S : Type}, Operations S → S)
    (hnat : ∀ {S T : Type} (op : Operations S) (target : Operations T) (eval : S → T),
      OperationMap op target eval → eval (prog op) = prog target)
    (d : ℕ → Bounds) (hd : prog (ops prec 0) = some d) : Contains (d 0) (prog realOperations) := by
  have h := box_sound (m := 0) prec (fun op _ => prog op) (fun op target eval he _ => hnat op target eval he)
    Fin.elim0 d hd Fin.elim0 (fun i => i.elim0)
  exact h

/-- Initial boxes for the camera ray, or failure. -/
def cameraBoxes (prec : ℕ) (spin pos dir hint : Fin 3 → Dyadic) : Option (Bounds × (Fin 10 → Bounds)) := do
  let p ← cameraPt spin pos dir (ops prec 0)
  let y ← collect fun i => cameraY spin pos dir hint (ops prec 0) i
  pure (p 0,fun i => y i 0)

theorem cameraBoxes_sound (prec : ℕ) (spin pos dir hint : Fin 3 → Dyadic) (PT : Bounds)
    (X : Fin 10 → Bounds) (h : cameraBoxes prec spin pos dir hint = some (PT,X)) :
    Contains PT (cameraPt spin pos dir realOperations) ∧
      ∀ i, Contains (X i) (cameraY spin pos dir hint realOperations i) := by
  simp only [cameraBoxes,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
  obtain ⟨p,hp,y,hy,hPX⟩ := h
  cases hPX
  refine ⟨constant_sound prec (fun op => cameraPt spin pos dir op)
    (fun op target eval he => cameraMomentum_nat spin pos dir op target eval he 0) p hp,fun i => ?_⟩
  exact constant_sound prec (fun op => cameraY spin pos dir hint op i)
    (fun op target eval he => cameraY_nat spin pos dir hint op target eval he i) _ (collect_some hy i)

/-! ### Escaping observables -/

section Observe
variable (spin : Fin 3 → Dyadic) {S : Type} (op : Operations S) (v : Fin 11 → S)

def obsX : Fin 3 → S := fun i => v ⟨i,by omega⟩
def obsP : Fin 4 → S := fun i => v ⟨3+i,by omega⟩
def obsF : Fin 4 → S := fun i => v ⟨7+i,by omega⟩

def obsGeometry : Geometry S := geometry op (fun i => op.constant (spin i)) (obsX v)

def spatialK : Fin 3 → S := fun i =>
  sum4 op (fun j => op.mul ((obsGeometry spin op v).inverse i.succ j) (obsP v j))

def kNormP : S := op.sqrt (dot3 op (spatialK spin op v) (spatialK spin op v))

def chordSqP (out : Fin 3 → Dyadic) : S :=
  let k := spatialK spin op v
  let kn := kNormP spin op v
  let o : Fin 3 → S := fun i => op.constant (out i)
  let on := op.sqrt (dot3 op o o)
  -- The squared chord: its enclosure contains 0 for an accurate direction, so no root.
  sum3 op fun i =>
    op.mul (op.sub (op.div (k i) kn) (op.div (o i) on)) (op.sub (op.div (k i) kn) (op.div (o i) on))

def redshiftP : S :=
  op.div (op.sqrt (op.neg ((obsGeometry spin op v).metric 0 0))) (obsP v 0)

def screenNormP : S :=
  op.sub (sum4 op fun i => sum4 op fun j =>
    op.mul (op.mul ((obsGeometry spin op v).metric i j) (obsF v i)) (obsF v j)) (op.constant 1)

def transversalityP : S := sum4 op fun i => op.mul (obsP v i) (obsF v i)

end Observe

section Naturality
variable (spin : Fin 3 → Dyadic) {S T : Type} (op : Operations S) (target : Operations T)
  (eval : S → T) (h : OperationMap op target eval) (v : Fin 11 → S)
include h

theorem obsGeometry_metric (i j : Fin 4) : eval ((obsGeometry spin op v).metric i j) =
    (obsGeometry spin target (fun k => eval (v k))).metric i j := by
  simp only [obsGeometry,map_geometry_metric h,h.constant]; rfl

theorem obsGeometry_inverse (i j : Fin 4) : eval ((obsGeometry spin op v).inverse i j) =
    (obsGeometry spin target (fun k => eval (v k))).inverse i j := by
  simp only [obsGeometry,map_geometry_inverse h,h.constant]; rfl

theorem spatialK_nat (i : Fin 3) : eval (spatialK spin op v i) = spatialK spin target (fun k => eval (v k)) i := by
  simp only [spatialK,map_sum4 h,h.mul,obsGeometry_inverse spin op target eval h]; rfl

theorem kNorm_nat : eval (kNormP spin op v) = kNormP spin target (fun k => eval (v k)) := by
  simp only [kNormP,h.sqrt,dot3,map_sum3 h,h.mul,spatialK_nat spin op target eval h]

theorem chord_nat (out : Fin 3 → Dyadic) :
    eval (chordSqP spin op v out) = chordSqP spin target (fun k => eval (v k)) out := by
  simp only [chordSqP,h.sqrt,dot3,map_sum3 h,h.mul,h.sub,h.div,h.constant,
    spatialK_nat spin op target eval h,kNorm_nat spin op target eval h]

theorem redshift_nat : eval (redshiftP spin op v) = redshiftP spin target (fun k => eval (v k)) := by
  simp only [redshiftP,h.div,h.sqrt,h.neg,obsGeometry_metric spin op target eval h]; rfl

theorem screenNorm_nat : eval (screenNormP spin op v) = screenNormP spin target (fun k => eval (v k)) := by
  simp only [screenNormP,h.sub,map_sum4 h,h.mul,h.constant,obsGeometry_metric spin op target eval h]; rfl

theorem transversality_nat : eval (transversalityP op v) = transversalityP target (fun k => eval (v k)) := by
  simp only [transversalityP,map_sum4 h,h.mul]; rfl

end Naturality

/-- Full phase input boxes: position, time momentum, spatial momentum, screen. -/
def fullBox (PT : Bounds) (B : Fin 10 → Bounds) (i : Fin 11) : Bounds :=
  if h : i.val < 3 then B ⟨i,by omega⟩ else if i.val = 3 then PT else B ⟨i-1,by omega⟩

noncomputable def fullVec (pt : ℝ) (y : Reduced) (i : Fin 11) : ℝ :=
  if h : i.val < 3 then y ⟨i,by omega⟩ else if i.val = 3 then pt else y ⟨i-1,by omega⟩

theorem fullVec_contains {PT : Bounds} {B : Fin 10 → Bounds} {pt : ℝ} {y : Reduced}
    (hpt : Contains PT pt) (hy : ∀ i, Contains (B i) (y i)) (i : Fin 11) :
    Contains (fullBox PT B i) (fullVec pt y i) := by
  unfold fullBox fullVec
  split_ifs
  · exact hy _
  · exact hpt
  · exact hy _

structure Observation where
  direction : Fin 3 → Dyadic
  redshift : Dyadic

def million : Dyadic := 1000000

def observe (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (B : Fin 10 → Bounds)
    (o : Observation) : Bool :=
  let v : Fin 11 → CheckedData.Data := fun i => boxD (fullBox PT B i)
  match kNormP spin (ops prec 0) v, chordSqP spin (ops prec 0) v o.direction,
    redshiftP spin (ops prec 0) v, screenNormP spin (ops prec 0) v, transversalityP (ops prec 0) v with
  | some kn, some c, some r, some sn, some tr =>
    decide (0 < (kn 0).lo) && decide (0 < dotProduct (fun i => o.direction i) (fun i => o.direction i)) &&
      decide (4*(c 0).hi*million*million ≤ 1) && decide (0 < (r 0).lo) &&
      decide (gapD o.redshift (r 0)*million ≤ (r 0).lo) &&
      decide (gapD 0 (sn 0)*million ≤ 1) && decide (gapD 0 (tr 0)*million ≤ 1)
  | _,_,_,_,_ => false

noncomputable section

def realDirection (spin : Fin 3 → Dyadic) (v : Fin 11 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (fun i => spatialK spin realOperations v i/kNormP spin realOperations v)

def unitOut (out : Fin 3 → Dyadic) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (fun i => (out i).toReal/Real.sqrt (∑ j, (out j).toReal^2))

theorem euclid_norm (f : Fin 3 → ℝ) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm f‖ = Real.sqrt (∑ i, f i^2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs,sq_abs]

theorem unit_of_scale (f : Fin 3 → ℝ) (n : ℝ) (hn : n = Real.sqrt (∑ i, f i^2)) (hpos : 0 < n) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => f i/n)‖ = 1 := by
  rw [euclid_norm]
  have hs : 0 < ∑ i, f i^2 := by
    by_contra hc
    rw [not_lt] at hc
    rw [hn,Real.sqrt_eq_zero'.mpr hc] at hpos
    exact lt_irrefl _ hpos
  have hn2 : n^2 = ∑ i, f i^2 := by rw [hn,Real.sq_sqrt hs.le]
  rw [show (∑ i, (f i/n)^2) = (∑ i, f i^2)/n^2 by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => div_pow _ _ _,hn2,
    div_self hs.ne',Real.sqrt_one]

theorem gap_zero {b : Bounds} {x : ℝ} (hx : Contains b x) : |x| ≤ (gapD 0 b).toReal := by
  have := CheckedData.gap_sound (a := 0) hx
  simpa [toReal_gapD] using this

/-- A successful observation check bounds the output direction's angle and
the static-observer redshift's relative error by 10⁻⁶, together with the
screen's norm and transversality residuals, for every state in the box. -/
theorem observe_sound (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (B : Fin 10 → Bounds)
    (o : Observation) (h : observe prec spin PT B o = true) (pt : ℝ) (hpt : Contains PT pt)
    (y : Reduced) (hy : ∀ i, Contains (B i) (y i)) :
    InnerProductGeometry.angle (realDirection spin (fullVec pt y)) (unitOut o.direction) ≤ 1/1000000 ∧
      0 < redshiftP spin realOperations (fullVec pt y) ∧
      |o.redshift.toReal-redshiftP spin realOperations (fullVec pt y)| ≤
        redshiftP spin realOperations (fullVec pt y)/1000000 ∧
      |screenNormP spin realOperations (fullVec pt y)| ≤ 1/1000000 ∧
      |transversalityP realOperations (fullVec pt y)| ≤ 1/1000000 := by
  set v := fullVec pt y
  have hv := fullVec_contains hpt hy
  dsimp only [observe] at h
  split at h
  case h_2 => simp at h
  case h_1 kn c r sn tr hkn hc hr hsn htr =>
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩ := h
  have ekn := box_sound prec (fun op v => kNormP spin op v) (fun op t e he v => kNorm_nat spin op t e he v)
    _ kn hkn v hv
  have ec := box_sound prec (fun op v => chordSqP spin op v o.direction)
    (fun op t e he v => chord_nat spin op t e he v o.direction) _ c hc v hv
  have er := box_sound prec (fun op v => redshiftP spin op v)
    (fun op t e he v => redshift_nat spin op t e he v) _ r hr v hv
  have esn := box_sound prec (fun op v => screenNormP spin op v)
    (fun op t e he v => screenNorm_nat spin op t e he v) _ sn hsn v hv
  have etr := box_sound prec (fun op v => transversalityP op v)
    (fun op t e he v => transversality_nat op t e he v) _ tr htr v hv

  have toR {a b : Dyadic} (hab : a ≤ b) : a.toReal ≤ b.toReal := dyadic_le hab
  have tlt {a b : Dyadic} (hab : a < b) : a.toReal < b.toReal := Dyadic.toReal_lt_toReal.mpr hab
  have hmil : million.toReal = 1000000 := by simp [million]
  refine ⟨?_,?_,?_,?_,?_⟩
  · -- direction
    have hknpos : 0 < kNormP spin realOperations v := by
      have := tlt h1; simp at this; linarith [ekn.1]
    have hsumk : kNormP spin realOperations v =
        Real.sqrt (∑ i, spatialK spin realOperations v i^2) := by
      simp only [kNormP,realOperations,dot3,sum3,Fin.sum_univ_three,pow_two]
    have hD : ‖realDirection spin v‖ = 1 := unit_of_scale _ _ hsumk hknpos
    have hosum : 0 < ∑ j, (o.direction j).toReal^2 := by
      have := tlt h2
      simp only [real_zero,dotProduct] at this
      rw [show (∑ i, o.direction i*o.direction i).toReal = ∑ j, (o.direction j).toReal^2 by
        rw [show (∑ i, o.direction i*o.direction i).toReal =
          Dyadic.toRealAddMonoidHom (∑ i, o.direction i*o.direction i) from rfl,map_sum]
        simp [Dyadic.toRealAddMonoidHom,Dyadic.toReal_mul,pow_two]] at this
      exact this
    have hU : ‖unitOut o.direction‖ = 1 :=
      unit_of_scale (fun i => (o.direction i).toReal) _ rfl (Real.sqrt_pos.mpr hosum)
    have hchord : ‖realDirection spin v-unitOut o.direction‖ =
        Real.sqrt (chordSqP spin realOperations v o.direction) := by
      rw [realDirection,unitOut,← map_sub,euclid_norm]
      simp only [chordSqP,realOperations,sum3,dot3,Fin.sum_univ_three,pow_two]
      rfl
    have hang := DirectionError.angle_le_twice_chord _ _ hD hU
    rw [hchord] at hang
    have hc3 := toR h3
    simp [Dyadic.toReal_mul,hmil] at hc3
    have hsq : chordSqP spin realOperations v o.direction ≤ (1/2000000)^2 := by
      nlinarith [ec.2]
    have hroot : Real.sqrt (chordSqP spin realOperations v o.direction) ≤ 1/2000000 := by
      calc _ ≤ Real.sqrt ((1/2000000)^2) := Real.sqrt_le_sqrt hsq
        _ = 1/2000000 := Real.sqrt_sq (by norm_num)
    linarith
  · have := tlt h4; simp at this; linarith [er.1]
  · have hg := CheckedData.gap_sound (a := o.redshift.toReal) er
    rw [← toReal_gapD] at hg
    have h5' := toR h5
    simp only [Dyadic.toReal_mul,hmil] at h5'
    rw [div_eq_mul_inv]
    nlinarith [er.1]
  · have h6' := toR h6
    simp only [Dyadic.toReal_mul,hmil,real_one] at h6'
    have := gap_zero esn
    linarith
  · have h7' := toR h7
    simp only [Dyadic.toReal_mul,hmil,real_one] at h7'
    have := gap_zero etr
    linarith

end

end BlackHole.RayObserve
