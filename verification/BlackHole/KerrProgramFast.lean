module
public import BlackHole.KerrProgram

/-! The same Kerr program with every vector and matrix materialized once.
`KerrProgram.rhs` binds them as functions, so executable evaluation would
recompute each entry at every use. Here they are `Vector` values, and
closures only read finished vectors. `rhsFast_eq` shows the two programs are
equal for every operation set, so all semantic results transfer. -/

@[expose] public section
namespace BlackHole.KerrProgram

variable {S : Type*}

@[simp] theorem vector_get_ofFn {n : ℕ} (f : Fin n → S) (i : Fin n) : (Vector.ofFn f).get i = f i := by
  simp only [Vector.get,Vector.toArray_ofFn,Array.getElem_ofFn]
  rfl

@[simp] theorem vector_get_ofFn' {n : ℕ} (f : Fin n → S) : (Vector.ofFn f).get = f :=
  funext (vector_get_ofFn f)

def geometryFast (op : Operations S) (a x : Fin 3 → S) : Geometry S :=
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
  let dr := Vector.ofFn fun (e : Fin 3) =>
    div (add (mul r (x e)) (mul axr (a e))) (sub (mul (c 2) r2) q)
  let spatial := Vector.ofFn fun (i : Fin 3) => div
    (add (sub (mul r (x i)) (cross op a x i)) (mul axr (a i))) r2aa
  let ell := Vector.ofFn (Fin.cases (c 1) spatial.get : Fin 4 → S)
  let dell := Vector.ofFn fun (e : Fin 3) => Vector.ofFn (Fin.cases (c 0) (fun i =>
    let basis : Fin 3 → S := fun j => if j=e then c 1 else c 0
    div (sub
      (add (sub (add (mul (dr.get e) (x i)) (mul r (basis i))) (cross op a basis i))
        (mul (sub (div (a e) r) (div (mul ax (dr.get e)) r2)) (a i)))
      (mul (mul (mul (spatial.get i) (c 2)) r) (dr.get e))) r2aa) : Fin 4 → S)
  let dH := Vector.ofFn fun (e : Fin 3) => mul H (sub (div (mul (c 3) (dr.get e)) r)
    (div (add (mul (mul (c 4) r3) (dr.get e)) (mul (mul (c 2) ax) (a e))) den))
  let sign : Fin 4 → S := fun i => if i=0 then op.neg (c 1) else c 1
  let eta : Fin 4 → Fin 4 → S := fun i j => if i=j then sign i else c 0
  let metric := Vector.ofFn fun i => Vector.ofFn fun j =>
    add (eta i j) (mul (mul (mul (c 2) H) (ell.get i)) (ell.get j))
  let inverse := Vector.ofFn fun i => Vector.ofFn fun j => sub (eta i j)
    (mul (mul (mul (mul (mul (c 2) H) (sign i)) (ell.get i)) (sign j)) (ell.get j))
  let derivative := Vector.ofFn fun e => Vector.ofFn fun i => Vector.ofFn fun j =>
    add (mul (mul (mul (c 2) (dH.get e)) (ell.get i)) (ell.get j))
      (mul (mul (c 2) H) (add (mul ((dell.get e).get i) (ell.get j))
        (mul (ell.get i) ((dell.get e).get j))))
  {
    radius := r
    metric := fun i j => (metric.get i).get j
    inverse := fun i j => (inverse.get i).get j
    derivative := fun e i j => ((derivative.get e).get i).get j }

def rhsFast (op : Operations S) (a : Fin 3 → S) (state : State S) : State S :=
  let c := op.constant
  let add := op.add
  let sub := op.sub
  let mul := op.mul
  let m := geometryFast op a state.position
  let dot := fun (u v : Fin 4 → S) => sum4 op (fun i => mul (u i) (v i))
  let k := Vector.ofFn fun i => sum4 op (fun j => mul (m.inverse i j) (state.momentum j))
  let ds := Vector.ofFn fun (e : Fin 3) => Vector.ofFn fun i =>
    sum4 op (fun j => mul (m.derivative e i j) (state.screen j))
  let dk := Vector.ofFn fun (e : Fin 3) => Vector.ofFn fun i =>
    sum4 op (fun j => mul (m.derivative e i j) (k.get j))
  let cov := Vector.ofFn fun (i : Fin 4) =>
    sub (add
      (sum3 op (fun e => mul (k.get e.succ) ((ds.get e).get i)))
      (sum3 op (fun e => mul (state.screen e.succ) ((dk.get e).get i))))
      (Fin.cases (c 0) (fun e => dot k.get (ds.get e).get) i)
  let half := op.div (c 1) (c 2)
  let momentum := Vector.ofFn (Fin.cases (c 0) (fun e => mul half (dot k.get (dk.get e).get)) :
    Fin 4 → S)
  let screen := Vector.ofFn fun (i : Fin 4) =>
    mul (op.neg half) (sum4 op (fun j => mul (m.inverse i j) (cov.get j)))
  {
    position := fun i => k.get i.succ
    momentum := momentum.get
    screen := screen.get }

theorem geometryFast_eq (op : Operations S) (a x : Fin 3 → S) :
    geometryFast op a x = geometry op a x := by
  simp only [geometryFast,geometry,vector_get_ofFn,vector_get_ofFn']

theorem rhsFast_eq (op : Operations S) (a : Fin 3 → S) (state : State S) :
    rhsFast op a state = rhs op a state := by
  simp only [rhsFast,rhs,geometryFast_eq,vector_get_ofFn,vector_get_ofFn']

end BlackHole.KerrProgram
