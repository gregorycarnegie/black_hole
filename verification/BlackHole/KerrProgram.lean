module
public import BlackHole.KerrArithmetic
public import BlackHole.DyadicInterval

/-! The finite arithmetic Kerr program. Operations are parameters so the same
expression can be evaluated in reals or proof-carrying interval jets. -/

@[expose] public section
noncomputable section
namespace BlackHole.KerrProgram

structure Operations (S : Type*) where
  constant : Dyadic → S
  add : S → S → S
  sub : S → S → S
  mul : S → S → S
  div : S → S → S
  neg : S → S
  sqrt : S → S

structure Geometry (S : Type*) where
  radius : S
  metric : Fin 4 → Fin 4 → S
  inverse : Fin 4 → Fin 4 → S
  derivative : Fin 3 → Fin 4 → Fin 4 → S

structure State (S : Type*) where
  position : Fin 3 → S
  momentum : Fin 4 → S
  screen : Fin 4 → S

def sum3 (op : Operations S) (f : Fin 3 → S) : S :=
  op.add (op.add (f 0) (f 1)) (f 2)

def sum4 (op : Operations S) (f : Fin 4 → S) : S :=
  op.add (op.add (op.add (f 0) (f 1)) (f 2)) (f 3)

def dot3 (op : Operations S) (a b : Fin 3 → S) : S := sum3 op (fun i => op.mul (a i) (b i))

def radius (op : Operations S) (a x : Fin 3 → S) : S :=
  let q := op.sub (dot3 op x x) (dot3 op a a)
  let ax := dot3 op a x
  op.sqrt (op.div (op.add q
    (op.sqrt (op.add (op.mul q q) (op.mul (op.mul (op.constant 4) ax) ax)))) (op.constant 2))

def cross (op : Operations S) (a x : Fin 3 → S) : Fin 3 → S :=
  ![op.sub (op.mul (a 1) (x 2)) (op.mul (a 2) (x 1)),
    op.sub (op.mul (a 2) (x 0)) (op.mul (a 0) (x 2)),
    op.sub (op.mul (a 0) (x 1)) (op.mul (a 1) (x 0))]

def geometry (op : Operations S) (a x : Fin 3 → S) : Geometry S :=
  let c := op.constant
  let add := op.add
  let sub := op.sub
  let mul := op.mul
  let div := op.div
  let aa := dot3 op a a
  let ax := dot3 op a x
  let q := sub (dot3 op x x) aa
  let r := radius op a x
  let r2 := mul r r
  let r3 := mul r2 r
  let den := add (mul r2 r2) (mul ax ax)
  let H := div r3 den
  let axr := div ax r
  let r2aa := add r2 aa
  let dr : Fin 3 → S := fun e => div (add (mul r (x e)) (mul axr (a e))) (sub (mul (c 2) r2) q)
  let spatial : Fin 3 → S := fun i => div
    (add (sub (mul r (x i)) (cross op a x i)) (mul axr (a i))) r2aa
  let ell : Fin 4 → S := Fin.cases (c 1) spatial
  let dell : Fin 3 → Fin 4 → S := fun e => Fin.cases (c 0) (fun i =>
    let basis : Fin 3 → S := fun j => if j=e then c 1 else c 0
    div (sub
      (add (sub (add (mul (dr e) (x i)) (mul r (basis i))) (cross op a basis i))
        (mul (sub (div (a e) r) (div (mul ax (dr e)) r2)) (a i)))
      (mul (mul (mul (spatial i) (c 2)) r) (dr e))) r2aa)
  let dH : Fin 3 → S := fun e => mul H (sub (div (mul (c 3) (dr e)) r)
    (div (add (mul (mul (c 4) r3) (dr e)) (mul (mul (c 2) ax) (a e))) den))
  let sign : Fin 4 → S := fun i => if i=0 then op.neg (c 1) else c 1
  let eta : Fin 4 → Fin 4 → S := fun i j => if i=j then sign i else c 0
  {
    radius := r
    metric := fun i j => add (eta i j) (mul (mul (mul (c 2) H) (ell i)) (ell j))
    inverse := fun i j => sub (eta i j)
      (mul (mul (mul (mul (mul (c 2) H) (sign i)) (ell i)) (sign j)) (ell j))
    derivative := fun e i j => add (mul (mul (mul (c 2) (dH e)) (ell i)) (ell j))
      (mul (mul (c 2) H) (add (mul (dell e i) (ell j)) (mul (ell i) (dell e j)))) }

def rhs (op : Operations S) (a : Fin 3 → S) (state : State S) : State S :=
  let c := op.constant
  let add := op.add
  let sub := op.sub
  let mul := op.mul
  let m := geometry op a state.position
  let mv := fun matrix v => fun i => sum4 op (fun j => mul (matrix i j) (v j))
  let dot := fun u v => sum4 op (fun i => mul (u i) (v i))
  let k := mv m.inverse state.momentum
  let cov : Fin 4 → S := fun i =>
    sub (add
      (sum3 op (fun e => mul (k e.succ) (mv (m.derivative e) state.screen i)))
      (sum3 op (fun e => mul (state.screen e.succ) (mv (m.derivative e) k i))))
      (Fin.cases (c 0) (fun e => dot k (mv (m.derivative e) state.screen)) i)
  let half := op.div (c 1) (c 2)
  {
    position := fun i => k i.succ
    momentum := Fin.cases (c 0) (fun e => mul half (dot k (mv (m.derivative e) k)))
    screen := fun i => mul (op.neg half) (mv m.inverse cov i) }

def realOperations : Operations ℝ := {
  constant := Dyadic.toReal, add := (·+·), sub := (·-·), mul := (·*·),
  div := (·/·), neg := Neg.neg, sqrt := Real.sqrt }

structure OperationMap (op : Operations S) (target : Operations T) (eval : S → T) : Prop where
  constant : ∀ q, eval (op.constant q) = target.constant q
  add : ∀ a b, eval (op.add a b) = target.add (eval a) (eval b)
  sub : ∀ a b, eval (op.sub a b) = target.sub (eval a) (eval b)
  mul : ∀ a b, eval (op.mul a b) = target.mul (eval a) (eval b)
  div : ∀ a b, eval (op.div a b) = target.div (eval a) (eval b)
  neg : ∀ a, eval (op.neg a) = target.neg (eval a)
  sqrt : ∀ a, eval (op.sqrt a) = target.sqrt (eval a)

abbrev Semantics (op : Operations S) (eval : S → ℝ) : Prop :=
  OperationMap op realOperations eval

def mapGeometry (eval : S → T) (g : Geometry S) : Geometry T := {
  radius := eval g.radius
  metric := fun i j => eval (g.metric i j)
  inverse := fun i j => eval (g.inverse i j)
  derivative := fun e i j => eval (g.derivative e i j) }

def mapState (eval : S → T) (state : State S) : State T := {
  position := fun i => eval (state.position i)
  momentum := fun i => eval (state.momentum i)
  screen := fun i => eval (state.screen i) }

variable {S T : Type*} {op : Operations S} {target : Operations T} {eval : S → T}

theorem map_sum3 (h : OperationMap op target eval) (f : Fin 3 → S) :
    eval (sum3 op f) = sum3 target (fun i => eval (f i)) := by
  simp [sum3,h.add]

theorem map_sum4 (h : OperationMap op target eval) (f : Fin 4 → S) :
    eval (sum4 op f) = sum4 target (fun i => eval (f i)) := by
  simp [sum4,h.add]

theorem map_cross (h : OperationMap op target eval) (a x : Fin 3 → S) (i : Fin 3) :
    eval (cross op a x i) = cross target (fun j => eval (a j)) (fun j => eval (x j)) i := by
  fin_cases i <;> simp [cross,h.sub,h.mul]

theorem map_cases (eval : S → T) (c : S) (f : Fin 3 → S) (i : Fin 4) :
    eval (Fin.cases c f i) = Fin.cases (eval c) (fun j => eval (f j)) i := by
  cases i using Fin.cases <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem map_geometry (h : OperationMap op target eval) (a x : Fin 3 → S) :
    mapGeometry eval (geometry op a x) =
      geometry target (fun i => eval (a i)) (fun i => eval (x i)) := by
  simp only [mapGeometry,geometry,dot3,radius,map_sum3 h,map_cross h,map_cases,
    h.constant,h.add,h.sub,h.mul,h.div,h.neg,h.sqrt,apply_ite]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem map_rhs (h : OperationMap op target eval) (a : Fin 3 → S) (state : State S) :
    mapState eval (rhs op a state) = rhs target (fun i => eval (a i)) (mapState eval state) := by
  have hi (i j : Fin 4) : eval ((geometry op a state.position).inverse i j) =
      (geometry target (fun k => eval (a k)) (fun k => eval (state.position k))).inverse i j :=
    congrArg (fun g => g.inverse i j) (map_geometry h a state.position)
  have hd (e : Fin 3) (i j : Fin 4) : eval ((geometry op a state.position).derivative e i j) =
      (geometry target (fun k => eval (a k)) (fun k => eval (state.position k))).derivative e i j :=
    congrArg (fun g => g.derivative e i j) (map_geometry h a state.position)
  simp only [mapState,rhs,map_sum3 h,map_sum4 h,map_cases,
    h.constant,h.add,h.sub,h.mul,h.div,h.neg,hi,hd]

theorem real_dot3 (a b : Fin 3 → ℝ) : dot3 realOperations a b = dotProduct a b := by
  simp [dot3,sum3,realOperations,dotProduct,Fin.sum_univ_succ]
  ring

theorem real_cross (a x : Fin 3 → ℝ) (i : Fin 3) :
    cross realOperations a x i = crossProduct a x i := by
  fin_cases i <;> simp [cross,realOperations,cross_apply]

theorem real_radius (a x : Fin 3 → ℝ) : radius realOperations a x = Cartesian.radius a x := by
  simp [radius,dot3,sum3,realOperations,Cartesian.radius,Cartesian.q,Cartesian.b,
    Calculus.kerrRadius,dotProduct,Fin.sum_univ_succ,pow_two,mul_assoc,add_assoc]

set_option maxHeartbeats 2000000 in
theorem real_metric (a x : Fin 3 → ℝ) (i j : Fin 4) :
    (geometry realOperations a x).metric i j = Cartesian.metric 1 a x i j := by
  have hd := real_dot3
  have hr := real_radius
  have hc := real_cross
  dsimp only [realOperations] at hd hr hc
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [geometry,realOperations,hd,hr,hc,Cartesian.metric,Cartesian.eta,Cartesian.ell,
      Cartesian.spatialEll,Cartesian.potential,Cartesian.b,Calculus.kerrH,pow_succ,mul_assoc]

set_option maxHeartbeats 2000000 in
theorem real_inverse (a x : Fin 3 → ℝ) (i j : Fin 4) :
    (geometry realOperations a x).inverse i j = KerrField.explicitInverse 1 a x i j := by
  have hd := real_dot3
  have hr := real_radius
  have hc := real_cross
  dsimp only [realOperations] at hd hr hc
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [geometry,realOperations,hd,hr,hc,KerrField.explicitInverse,KerrField.minkowski,
      KerrField.raisedEll,KerrField.signature,Cartesian.ell,Cartesian.spatialEll,
      Cartesian.potential,Cartesian.b,Calculus.kerrH,Matrix.vecMulVec,Matrix.diagonal_apply,pow_succ,mul_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem real_derivative (a x : Fin 3 → ℝ) (e : Fin 3) (i j : Fin 4) :
    (geometry realOperations a x).derivative e i j = Cartesian.metricD 1 a x e i j := by
  have hd := real_dot3
  have hr := real_radius
  have hc := real_cross
  have hb (d : Fin 3) : Cartesian.basis d = (fun k => if k=d then 1 else 0) := rfl
  dsimp only [realOperations] at hd hr hc
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [geometry,realOperations,hd,hr,hc,Cartesian.metricD,Cartesian.ell,Cartesian.ellD,
      Cartesian.spatialEll,Cartesian.spatialEllD,Cartesian.potential,Cartesian.potentialD,
      Cartesian.radiusD,hb,Cartesian.basis,Cartesian.q,Cartesian.b,Calculus.kerrH,pow_succ,mul_assoc]

def toPhase (state : State ℝ) : KerrField.Phase := (state.position,state.momentum,state.screen)

def ofPhase (state : KerrField.Phase) : State ℝ := ⟨state.1,state.2.1,state.2.2⟩

theorem real_sum3 (f : Fin 3 → ℝ) : sum3 realOperations f = ∑ i, f i := by
  simp [sum3,realOperations,Fin.sum_univ_succ,add_assoc]

theorem real_sum4 (f : Fin 4 → ℝ) : sum4 realOperations f = ∑ i, f i := by
  simp [sum4,realOperations,Fin.sum_univ_succ,add_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem real_rhs (a : Fin 3 → ℝ) (state : State ℝ) :
    toPhase (rhs realOperations a state) = KerrField.arithmeticRhs 1 a (toPhase state) := by
  simp only [toPhase,rhs,KerrField.arithmeticRhs,real_sum3,real_sum4,real_inverse,real_derivative]
  simp only [realOperations]
  apply Prod.ext
  · funext i
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · apply Prod.ext
    · funext i
      cases i using Fin.cases with
      | zero => simp [Transport.momentumForce,KerrField.metricD]
      | succ i =>
        simp [Transport.momentumForce,KerrField.metricD,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
        ring
    · funext i
      simp [KerrField.screenCovector,KerrField.metricD,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] 

theorem real_rhs_exact (a : Fin 3 → ℝ) (state : State ℝ)
    (hr : 0 < Cartesian.radius a state.position) :
    toPhase (rhs realOperations a state) = KerrField.phaseRhs 1 a (toPhase state) :=
  (real_rhs a state).trans (KerrField.arithmetic_rhs_eq 1 a (toPhase state) hr)

inductive Component where
  | position : Fin 3 → Component
  | momentum : Fin 4 → Component
  | screen : Fin 4 → Component

def State.get (state : State S) : Component → S
  | .position i => state.position i
  | .momentum i => state.momentum i
  | .screen i => state.screen i

def phaseGet (state : KerrField.Phase) : Component → ℝ
  | .position i => state.1 i
  | .momentum i => state.2.1 i
  | .screen i => state.2.2 i

theorem map_get (eval : S → ℝ) (state : State S) (c : Component) :
    phaseGet (toPhase (mapState eval state)) c = eval (state.get c) := by cases c <;> rfl

end BlackHole.KerrProgram
