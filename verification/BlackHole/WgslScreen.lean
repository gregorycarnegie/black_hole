module

public import BlackHole.WgslExpr

/-! All-input WGSL error bounds for `spatial_unit` and `screen_frame` in
`geodesic.wesl` (obligation F2).

```
fn spatial_unit(v: vec3<f32>, gamma: mat3x3<f32>) -> vec3<f32> {
    let scale=max(max(abs(v.x),abs(v.y)),abs(v.z));
    if scale==0.0 { return v; }
    let scaled=v/scale;
    return scaled*inverseSqrt(max(dot(scaled,gamma*scaled),1.0e-20));
}
fn screen_frame(ray: Ray, m: Metric) -> mat3x3<f32> {
    let k = m.inv*ray.p;
    let shift = -m.inv[0].yzw/m.inv[0][0];
    let gamma = spatial_metric(m);
    let n = spatial_unit(k.yzw+shift*k.x,gamma);
    let f = ray.screen.yzw-k.yzw*(ray.screen.x/k.x);
    let e1 = spatial_unit(f-n*dot(n,gamma*f),gamma);
    let e2 = spatial_unit(cross(gamma*n,gamma*e1),gamma);
    return mat3x3<f32>(e1,e2,n);
}
```

Because `scale ≥ 0` in both evaluations, `scale == 0.0` is the branch
`¬(0 < scale)`, encoded as `-scale < 0`. Inputs: `g` 0–15, `inv` 16–31 (entry
`4 i + j`), momentum 32–35 and screen 36–39. Matrix layout only relabels
inputs. The `Safe` conditions are that `scale`, `inv[0][0]` and `k.x` exceed
their own errors, and that the inverse-square-root argument stays positive. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslScreen
open Wgsl WgslExpr GExpr

def f32_1em20 : ℚ := 1547425/154742504910672534362390528

def g (i j : Fin 4) : GExpr := input (4*i+j)
def inv (i j : Fin 4) : GExpr := input (16+4*i+j)
def p (i : Fin 4) : GExpr := input (32+i)
def scr (i : Fin 4) : GExpr := input (36+i)

def sum3 (t : Fin 3 → GExpr) : GExpr := add (add (t 0) (t 1)) (t 2)
def sum4 (t : Fin 4 → GExpr) : GExpr := add (add (add (t 0) (t 1)) (t 2)) (t 3)

/-- The spatial metric `gamma`. -/
def gamma (i j : Fin 3) : GExpr := g i.succ j.succ
def gammaMul (v : Fin 3 → GExpr) (i : Fin 3) : GExpr := sum3 fun j => mul (gamma i j) (v j)
def dot3 (a b : Fin 3 → GExpr) : GExpr := sum3 fun i => mul (a i) (b i)

def spatialUnit (v : Fin 3 → GExpr) (i : Fin 3) : GExpr :=
  let scale := max (max (abs (v 0)) (abs (v 1))) (abs (v 2))
  let scaled : Fin 3 → GExpr := fun j => div (v j) scale
  lt (neg scale) 0
    (mul (scaled i) (invsqrt (max (dot3 scaled (gammaMul scaled)) (const f32_1em20))))
    (v i)

def k (i : Fin 4) : GExpr := sum4 fun j => mul (inv i j) (p j)
def shift (i : Fin 3) : GExpr := div (neg (inv i.succ 0)) (inv 0 0)
def nVec : Fin 3 → GExpr := spatialUnit fun i => add (k i.succ) (mul (shift i) (k 0))
def fVec (i : Fin 3) : GExpr := sub (scr i.succ) (mul (k i.succ) (div (scr 0) (k 0)))
def e1 : Fin 3 → GExpr :=
  spatialUnit fun i => sub (fVec i) (mul (nVec i) (dot3 nVec (gammaMul fVec)))
def cross (u v : Fin 3 → GExpr) : Fin 3 → GExpr :=
  ![sub (mul (u 1) (v 2)) (mul (u 2) (v 1)),
    sub (mul (u 2) (v 0)) (mul (u 0) (v 2)),
    sub (mul (u 0) (v 1)) (mul (u 1) (v 0))]
def e2 : Fin 3 → GExpr := spatialUnit (cross (gammaMul nVec) (gammaMul e1))

/-- The three frame columns `e1`, `e2`, `n`. -/
def frame (col : Fin 3) (i : Fin 3) : GExpr :=
  if col = 0 then e1 i else if col = 1 then e2 i else nVec i

theorem screen_frame_error (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (col i : Fin 3) (y : ℝ)
    (hs : (frame col i).Safe v E) (hy : (frame col i).Computes w y) :
    |y-(frame col i).exact v| ≤ (frame col i).bound v E :=
  error (frame col i) v w E hw y hs hy

theorem spatial_unit_error (vec : Fin 3 → GExpr) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i)
    (i : Fin 3) (y : ℝ) (hs : (spatialUnit vec i).Safe v E) (hy : (spatialUnit vec i).Computes w y) :
    |y-(spatialUnit vec i).exact v| ≤ (spatialUnit vec i).bound v E :=
  error (spatialUnit vec i) v w E hw y hs hy

end BlackHole.WgslScreen
