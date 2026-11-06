module
public import BlackHole.RayObserve
public import BlackHole.KerrCamera

/-! Physical meaning of the exact camera state. For a camera with positive
Kerr radius, a direction and screen hint that are not degenerate, the state
`RayObserve.cameraMomentum`/`cameraScreen` is a null covector with Eulerian
energy one, and its screen is a unit spacelike vector transverse to the ray.
`cameraChecks` establishes the three nondegeneracy hypotheses by checked
evaluation, so a successful certificate implies them. -/

@[expose] public section
open Set
namespace BlackHole.CameraPhysics
open DyadicInterval KerrProgram StepCheck RayEvents RayObserve

noncomputable section

variable (spin pos dir hint : Fin 3 → Dyadic)

def a : Cartesian.Space := CheckedFunction.spinValue spin
def x : Cartesian.Space := fun i => (pos i).toReal
def G : Matrix (Fin 4) (Fin 4) ℝ := KerrField.metric 1 (a spin) (x pos)
def Inv : Matrix (Fin 4) (Fin 4) ℝ := KerrField.explicitInverse 1 (a spin) (x pos)
def d0 : Fin 3 → ℝ := fun i => (dir i).toReal
def h0 : Fin 3 → ℝ := fun i => (hint i).toReal
def dhat : Fin 3 → ℝ := fun i => d0 dir i/Real.sqrt (ADM.spatial (G spin pos) (d0 dir) (d0 dir))
def s0 : Fin 3 → ℝ := fun i =>
  h0 hint i-ADM.spatial (G spin pos) (h0 hint) (dhat spin pos dir)*dhat spin pos dir i
def shat : Fin 3 → ℝ := fun i => s0 spin pos dir hint i/Real.sqrt (ADM.spatial (G spin pos) (s0 spin pos dir hint) (s0 spin pos dir hint))

/-- The camera's past null tangent in ADM form. -/
def tangent : Fin 4 → ℝ := ADM.pastTangent (Inv spin pos) (dhat spin pos dir)

/-- The camera screen as a spacetime vector with zero time component. -/
def screen4 : Fin 4 → ℝ := Fin.cases 0 (shat spin pos dir hint)

theorem inv_symm (i j : Fin 4) : Inv spin pos i j = Inv spin pos j i := by
  simp only [Inv,KerrField.explicitInverse,Matrix.sub_apply,Matrix.smul_apply,KerrField.minkowski,
    Matrix.diagonal_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  by_cases h : i = j
  · subst h; rfl
  · simp [h,Ne.symm h,mul_comm]

theorem sum_spatial (u v : Fin 3 → ℝ) :
    (∑ i, ∑ j, u i*Cartesian.metric 1 (fun i => (spin i).toReal) (fun i => (pos i).toReal)
      i.succ j.succ*v j) = ADM.spatial (G spin pos) u v := by
  simp only [ADM.spatial,G,KerrField.metric,Matrix.of_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [show Cartesian.metric 1 (a spin) (x pos) = Cartesian.metric 1 (fun i => (spin i).toReal)
      (fun i => (pos i).toReal) from rfl]; ring

theorem spatial_symm (u v : Fin 3 → ℝ) :
    ADM.spatial (G spin pos) u v = ADM.spatial (G spin pos) v u := by
  unfold ADM.spatial
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show G spin pos j.succ i.succ = G spin pos i.succ j.succ from KerrField.metric_symmetric 1 _ _ _ _]
  ring

theorem spatial_unit (v : Fin 3 → ℝ) (hv : 0 < ADM.spatial (G spin pos) v v) :
    ADM.spatial (G spin pos) (fun i => v i/Real.sqrt (ADM.spatial (G spin pos) v v))
      (fun i => v i/Real.sqrt (ADM.spatial (G spin pos) v v)) = 1 := by
  set n := Real.sqrt (ADM.spatial (G spin pos) v v)
  have hn : n^2 = ADM.spatial (G spin pos) v v := Real.sq_sqrt hv.le
  have hn0 : n ≠ 0 := by positivity
  have : ADM.spatial (G spin pos) (fun i => v i/n) (fun i => v i/n) = ADM.spatial (G spin pos) v v/n^2 := by
    simp only [ADM.spatial,Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [this,hn,div_self hv.ne']

theorem spatial_div_right (u v : Fin 3 → ℝ) (c : ℝ) :
    ADM.spatial (G spin pos) u (fun i => v i/c) = ADM.spatial (G spin pos) u v/c := by
  simp only [ADM.spatial,Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem spatial_sub_right (u v w : Fin 3 → ℝ) (c : ℝ) :
    ADM.spatial (G spin pos) u (fun i => v i-c*w i) =
      ADM.spatial (G spin pos) u v-c*ADM.spatial (G spin pos) u w := by
  simp only [ADM.spatial,Finset.mul_sum,← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The real camera program is the ADM past null initialization. -/
theorem real_cameraMomentum (h00 : Inv spin pos 0 0 < 0) :
    cameraMomentum spin pos dir realOperations = (G spin pos).mulVec (tangent spin pos dir) := by
  funext i
  have hE : KerrField.explicitInverse 1 (fun i => (spin i).toReal) (fun i => (pos i).toReal) =
    Inv spin pos := rfl
  simp only [cameraMomentum,real_metric,real_inverse,real_sum3,real_sum4]
  simp only [realOperations,real_one,hE,sum_spatial,Matrix.mulVec,dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Cartesian.metric 1 (fun i => (spin i).toReal) (fun i => (pos i).toReal) i j = G spin pos i j
    from rfl]
  congr 1
  have hs : 0 < -Inv spin pos 0 0 := neg_pos.mpr h00
  set q := Real.sqrt (-Inv spin pos 0 0) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hs
  have hInv : Inv spin pos 0 0 = -q^2 := by rw [hq,Real.sq_sqrt hs.le]; ring
  cases j using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero,tangent,ADM.pastTangent,ADM.lapse,← hq]
    ring
  | succ j =>
    simp only [Fin.cases_succ,tangent,ADM.pastTangent,ADM.shift,ADM.lapse,← hq,dhat,d0]
    rw [inv_symm spin pos j.succ 0,hInv]
    field_simp
    ring_nf
    rfl

theorem real_cameraScreen :
    cameraScreen spin pos dir hint realOperations = shat spin pos dir hint := by
  funext i
  simp only [cameraScreen,real_metric,real_sum3]
  simp only [realOperations,sum_spatial]
  rfl

theorem dot_mulVec_expand (g : Matrix (Fin 4) (Fin 4) ℝ) (hsym : ∀ i j, g i j = g j i)
    (k : Fin 4 → ℝ) : dotProduct k (g.mulVec k) = ADM.norm g (k 0) (fun i => k i.succ) := by
  simp only [dotProduct,Matrix.mulVec,ADM.norm,ADM.spatial,Fin.sum_univ_four,Fin.sum_univ_three]
  rw [hsym 1 0,hsym 2 0,hsym 3 0]
  simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  rw [show (Fin.succ 2 : Fin 4) = 3 from rfl]
  ring

theorem G_symm : ∀ i j, G spin pos i j = G spin pos j i :=
  fun i j => KerrField.metric_symmetric 1 _ _ i j

/-- The exact camera state is a null covector with Eulerian energy one; its
screen is a unit spacelike vector orthogonal to the ray. -/
theorem camera_physics (hr : 0 < Cartesian.radius (a spin) (x pos))
    (hd : 0 < ADM.spatial (G spin pos) (d0 dir) (d0 dir))
    (hs : 0 < ADM.spatial (G spin pos) (s0 spin pos dir hint) (s0 spin pos dir hint)) :
    let p := cameraMomentum spin pos dir realOperations
    let f : Fin 4 → ℝ := Fin.cases 0 (cameraScreen spin pos dir hint realOperations)
    let inv := (G spin pos)⁻¹
    dotProduct (inv.mulVec p) p = 0 ∧
      dotProduct p (ADM.observer inv) = 1 ∧
      0 < ADM.observer inv 0 ∧
      dotProduct f ((G spin pos).mulVec f) = 1 ∧
      dotProduct p f = 0 := by
  intro p f inv
  have hinvE : inv = Inv spin pos := KerrField.inverse_eq_explicit 1 _ _ hr
  have hmul : G spin pos*Inv spin pos = 1 := KerrField.metric_mul_explicitInverse 1 _ _ hr
  have h00 : Inv spin pos 0 0 < 0 := by
    have := KerrField.inverse_time_negative 1 (a spin) (x pos) (by norm_num) hr
    rwa [show (KerrField.metric 1 (a spin) (x pos))⁻¹ = Inv spin pos from hinvE] at this
  have hp : p = (G spin pos).mulVec (tangent spin pos dir) := real_cameraMomentum spin pos dir h00
  have hf : f = screen4 spin pos dir hint := by
    simp only [f,real_cameraScreen]; rfl
  have hdir := spatial_unit spin pos (d0 dir) hd
  have hcam := KerrField.camera_initialization 1 (a spin) (x pos) (dhat spin pos dir) (by norm_num) hr hdir
  simp only [show (KerrField.metric 1 (a spin) (x pos))⁻¹ = Inv spin pos from hinvE] at hcam
  obtain ⟨hfut,-,henergy,hnull⟩ := hcam
  rw [hinvE,hf,hp]
  have hshift := (ADM.shift_equations (G spin pos) (Inv spin pos) hmul h00.ne).1
  -- spatial momentum components reduce to the spatial metric applied to the direction
  have hmom (i : Fin 3) : (G spin pos).mulVec (tangent spin pos dir) i.succ =
      ∑ j, G spin pos i.succ j.succ*dhat spin pos dir j := by
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,tangent,ADM.pastTangent,Fin.cases_zero,
      Fin.cases_succ]
    have hsh := hshift i
    have hl := (ADM.lapse_identity (Inv spin pos) h00).1
    simp only [Fin.sum_univ_succ] at hsh
    field_simp
    simp only [mul_add]
    rw [← hsh]
    ring
  have hdir' : ADM.spatial (G spin pos) (dhat spin pos dir) (dhat spin pos dir) = 1 := hdir
  have hnorm0 (v : Fin 3 → ℝ) : ADM.norm (G spin pos) 0 v = ADM.spatial (G spin pos) v v := by
    simp [ADM.norm]
  refine ⟨?_,henergy,hfut,?_,?_⟩
  · rw [Matrix.mulVec_mulVec,(mul_eq_one_comm.mp hmul),Matrix.one_mulVec,
      dot_mulVec_expand _ (G_symm spin pos)]
    have e1 : tangent spin pos dir 0 = -1/ADM.lapse (Inv spin pos) := rfl
    have e2 : (fun i => tangent spin pos dir i.succ) =
        dhat spin pos dir+(1/ADM.lapse (Inv spin pos)) • ADM.shift (Inv spin pos) := by
      funext i
      simp only [tangent,ADM.pastTangent,Fin.cases_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [e1,e2]
    exact hnull
  · rw [dot_mulVec_expand _ (G_symm spin pos),show screen4 spin pos dir hint 0 = 0 from rfl,hnorm0]
    exact spatial_unit spin pos _ hs
  · have hz : ADM.spatial (G spin pos) (dhat spin pos dir) (shat spin pos dir hint) = 0 := by
      unfold shat
      rw [spatial_div_right]
      unfold s0
      rw [spatial_sub_right,spatial_symm spin pos (dhat spin pos dir) (h0 hint),hdir']
      simp
    rw [spatial_symm] at hz
    rw [dotProduct,Fin.sum_univ_succ]
    simp only [screen4,Fin.cases_zero,Fin.cases_succ,mul_zero,zero_add,hmom]
    rw [← hz]
    simp only [ADM.spatial,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

/-! ### Checked nondegeneracy -/

variable (spin pos dir hint : Fin 3 → Dyadic)

section Programs
variable {S : Type} (op : Operations S)

def cameraRadiusP : S := radius op (fun i => op.constant (spin i)) (fun i => op.constant (pos i))

def cameraSdot (u v : Fin 3 → S) : S :=
  let m := geometry op (fun i => op.constant (spin i)) (fun i => op.constant (pos i))
  sum3 op (fun i => sum3 op (fun j => op.mul (op.mul (u i) (m.metric i.succ j.succ)) (v j)))

def cameraDirP : S := cameraSdot spin pos op (fun i => op.constant (dir i)) (fun i => op.constant (dir i))

def cameraHintP : S :=
  let d0 : Fin 3 → S := fun i => op.constant (dir i)
  let d : Fin 3 → S := fun i => op.div (d0 i) (op.sqrt (cameraSdot spin pos op d0 d0))
  let h0 : Fin 3 → S := fun i => op.constant (hint i)
  let s0 : Fin 3 → S := fun i => op.sub (h0 i) (op.mul (cameraSdot spin pos op h0 d) (d i))
  cameraSdot spin pos op s0 s0

end Programs

section Nat
variable {S T : Type} (op : Operations S) (target : Operations T) (eval : S → T)
  (h : OperationMap op target eval)
include h

theorem cameraSdot_nat (u v : Fin 3 → S) :
    eval (cameraSdot spin pos op u v) = cameraSdot spin pos target (fun i => eval (u i)) (fun i => eval (v i)) := by
  simp only [cameraSdot,map_sum3 h,h.mul,map_geometry_metric h,h.constant]

theorem cameraRadius_nat : eval (cameraRadiusP spin pos op) = cameraRadiusP spin pos target := by
  simp only [cameraRadiusP,map_radius h,h.constant]

theorem cameraDir_nat : eval (cameraDirP spin pos dir op) = cameraDirP spin pos dir target := by
  simp only [cameraDirP,cameraSdot_nat spin pos op target eval h,h.constant]

theorem cameraHint_nat : eval (cameraHintP spin pos dir hint op) = cameraHintP spin pos dir hint target := by
  simp only [cameraHintP,cameraSdot_nat spin pos op target eval h,h.constant,h.sub,h.mul,h.div,h.sqrt]

end Nat

noncomputable section

theorem real_cameraSdot (u v : Fin 3 → ℝ) :
    cameraSdot spin pos realOperations u v = ADM.spatial (G spin pos) u v := by
  simp only [cameraSdot,real_metric,real_sum3]
  simp only [realOperations,sum_spatial]

theorem real_cameraRadius : cameraRadiusP spin pos realOperations = Cartesian.radius (a spin) (x pos) :=
  real_radius _ _

theorem real_cameraDir : cameraDirP spin pos dir realOperations = ADM.spatial (G spin pos) (d0 dir) (d0 dir) :=
  real_cameraSdot spin pos _ _

theorem real_cameraHint :
    cameraHintP spin pos dir hint realOperations =
      ADM.spatial (G spin pos) (s0 spin pos dir hint) (s0 spin pos dir hint) := by
  simp only [cameraHintP,real_cameraSdot]
  rfl

end

def positive (prec : ℕ) (prog : ∀ {S : Type}, Operations S → S) : Bool :=
  match prog (ops prec 0) with
  | some d => decide (0 < (d 0).lo)
  | none => false

/-- The camera radius, direction norm and transverse hint norm are all positive. -/
def cameraChecks (prec : ℕ) : Bool :=
  positive prec (cameraRadiusP spin pos) && positive prec (cameraDirP spin pos dir) &&
    positive prec (cameraHintP spin pos dir hint)

theorem positive_sound (prec : ℕ) (prog : ∀ {S : Type}, Operations S → S)
    (hnat : ∀ {S T : Type} (op : Operations S) (target : Operations T) (eval : S → T),
      OperationMap op target eval → eval (prog op) = prog target)
    (h : positive prec prog = true) : 0 < prog realOperations := by
  unfold positive at h
  split at h
  case h_2 => simp at h
  case h_1 d hd =>
  have hc := constant_sound prec prog hnat d hd
  have := Dyadic.toReal_lt_toReal.mpr (of_decide_eq_true h)
  simp at this
  linarith [hc.1]

theorem cameraChecks_sound (prec : ℕ) (h : cameraChecks spin pos dir hint prec = true) :
    0 < Cartesian.radius (a spin) (x pos) ∧ 0 < ADM.spatial (G spin pos) (d0 dir) (d0 dir) ∧
      0 < ADM.spatial (G spin pos) (s0 spin pos dir hint) (s0 spin pos dir hint) := by
  simp only [cameraChecks,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  refine ⟨?_,?_,?_⟩
  · rw [← real_cameraRadius]
    exact positive_sound prec (cameraRadiusP spin pos) (fun op t e he => cameraRadius_nat spin pos op t e he) h1
  · rw [← real_cameraDir]
    exact positive_sound prec (cameraDirP spin pos dir) (fun op t e he => cameraDir_nat spin pos dir op t e he) h2
  · rw [← real_cameraHint]
    exact positive_sound prec (cameraHintP spin pos dir hint)
      (fun op t e he => cameraHint_nat spin pos dir hint op t e he) h3

end BlackHole.CameraPhysics
