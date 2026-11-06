module

public import BlackHole.WgslExpr

/-! All-input WGSL error bounds for `add_kerr` in `geodesic.wesl` (obligation F2).

```
let a = mass * spin / max(1.0, length(spin)/0.999);
let a2 = dot(a,a);  let ax = dot(a,x);  let raw_r = kerr_radius(x,a);
let horizon = mass + sqrt(max(mass*mass-a2, 0.0));
m.clearance = min(m.clearance, raw_r-horizon);
let r = max(raw_r, 0.8*horizon);  let r2 = r*r;  let den = r2*r2 + ax*ax;
let h = mass*r*r2/den;
let numerator = r*x - cross(a,x) + (ax/r)*a;
let ell = vec4<f32>(1.0, numerator/(r2+a2));
let dr = (r*x + (ax/r)*a) / max(2.0*r2-dot(x,x)+a2, 1.0e-12);
// per axis j: dh, dn, dl and deriv[j] = 2 dh ll + 2 h (dl ell^T + ell dl^T)
m.g += 2.0*h*ll;  m.dx += deriv[0]; ...
let raised = m.inv*ell;  let divisor = 1.0 + 2.0*h*dot(ell,raised);
if divisor <= 1.0e-6 { m.valid = false; return m; }
m.inv -= (2.0*h/divisor)*outer(raised,raised);
m.valid = m.valid && m.inv[0][0] < -1.0e-6;
```

Inputs: `x` 0–2, `a` 3–5 (the scaled spin actually used), `mass` 6, the
computed Kerr radius `raw_r` 7 (its error is `WgslKerrRadius.kerr_radius_error`,
at most `160u·r`), incoming `g` 8–23, `inv` 24–39, `dx/dy/dz` 40–87 and
clearance 88. The scaling of `spin` into `a` is `spinScale` below.

`add_kerr_error` bounds every updated metric, inverse, derivative and
clearance entry by the running bound of `WgslExpr`, for every input where its
`Safe` conditions hold. Those conditions are exactly that each divisor (`r`,
`den`, `r²+a²`, the floored radial denominator, the Sherman–Morrison divisor)
is farther from zero than its own error, that the horizon's square-root
argument stays positive, and that the computed divisor is on the same side of
the binary32 value of `1e-6` as the exact one. The floors (`max(raw_r, 0.8 horizon)`, the `1e-12`
floor, `max(·, 0)`) and `min` for the clearance need no condition.
`flag_agree` shows the `valid` comparisons agree whenever the compared value
is farther from its threshold than its error. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslAddKerr
open Wgsl WgslExpr GExpr

def c (r : ℝ) : GExpr := const r

/-! The shader's decimal literals as the binary32 values it actually uses. -/
def f32_0_8 : ℝ := 13421773/16777216
def f32_0_999 : ℝ := 16760439/16777216
def f32_1em12 : ℝ := 2305843/2305843009213693952
def f32_1em6 : ℝ := 8796093/8796093022208
def xs (i : Fin 3) : GExpr := input i
def as (i : Fin 3) : GExpr := input (3+i)
def mass : GExpr := input 6
def rawR : GExpr := input 7
def g0 (i j : Fin 4) : GExpr := input (8+4*i+j)
def inv0 (i j : Fin 4) : GExpr := input (24+4*i+j)
def d0 (e : Fin 3) (i j : Fin 4) : GExpr := input (40+16*e+4*i+j)
def clear0 : GExpr := input 88

def sum3 (t : Fin 3 → GExpr) : GExpr := add (add (t 0) (t 1)) (t 2)
def sum4 (t : Fin 4 → GExpr) : GExpr := add (add (add (t 0) (t 1)) (t 2)) (t 3)
def dot3 (u v : Fin 3 → GExpr) : GExpr := sum3 fun i => mul (u i) (v i)
def cross (u v : Fin 3 → GExpr) : Fin 3 → GExpr :=
  ![sub (mul (u 1) (v 2)) (mul (u 2) (v 1)),
    sub (mul (u 2) (v 0)) (mul (u 0) (v 2)),
    sub (mul (u 0) (v 1)) (mul (u 1) (v 0))]

def a2 : GExpr := dot3 as as
def ax : GExpr := dot3 as xs
def horizon : GExpr := add mass (sqrt (max (sub (mul mass mass) a2) (c 0)))
def clearance : GExpr := min clear0 (sub rawR horizon)
def r : GExpr := max rawR (mul (c f32_0_8) horizon)
def r2 : GExpr := mul r r
def den : GExpr := add (mul r2 r2) (mul ax ax)
def h : GExpr := div (mul (mul mass r) r2) den
def axr : GExpr := div ax r
def numerator (i : Fin 3) : GExpr := add (sub (mul r (xs i)) (cross as xs i)) (mul axr (as i))
def r2a2 : GExpr := add r2 a2
def ell (i : Fin 4) : GExpr := Fin.cases (c 1) (fun i => div (numerator i) r2a2) i
def radialDen : GExpr := max (add (sub (mul (c 2) r2) (dot3 xs xs)) a2) (c f32_1em12)
def dr (j : Fin 3) : GExpr := div (add (mul r (xs j)) (mul axr (as j))) radialDen
def basis (j i : Fin 3) : GExpr := c (if i = j then 1 else 0)
def dh (j : Fin 3) : GExpr :=
  mul h (sub (div (mul (c 3) (dr j)) r)
    (div (add (mul (mul (mul (c 4) r) r2) (dr j)) (mul (mul (c 2) ax) (as j))) den))
def dn (j i : Fin 3) : GExpr :=
  add (sub (add (mul (dr j) (xs i)) (mul r (basis j i))) (cross as (basis j) i))
    (mul (sub (div (as j) r) (div (mul ax (dr j)) r2)) (as i))
def dl (j : Fin 3) (i : Fin 4) : GExpr :=
  Fin.cases (c 0) (fun i => div (sub (dn j i) (mul (mul (mul (ell i.succ) (c 2)) r) (dr j))) r2a2) i

/-- Updated metric entries `g + 2 h ell ell^T`. -/
def gOut (i j : Fin 4) : GExpr := add (g0 i j) (mul (mul (mul (c 2) h) (ell i)) (ell j))
/-- Updated derivative entries `d + 2 dh ell ell^T + 2 h (dl ell^T + ell dl^T)`. -/
def dOut (e : Fin 3) (i j : Fin 4) : GExpr :=
  add (d0 e i j) (add (mul (mul (mul (c 2) (dh e)) (ell i)) (ell j))
    (mul (mul (c 2) h) (add (mul (dl e i) (ell j)) (mul (ell i) (dl e j)))))
def raised (i : Fin 4) : GExpr := sum4 fun j => mul (inv0 i j) (ell j)
def divisor : GExpr := add (c 1) (mul (mul (c 2) h) (sum4 fun i => mul (ell i) (raised i)))
/-- Updated inverse entries; the early return keeps the incoming inverse. -/
def invOut (i j : Fin 4) : GExpr :=
  lt (neg divisor) (-f32_1em6)
    (sub (inv0 i j) (mul (div (mul (c 2) h) divisor) (mul (raised i) (raised j))))
    (inv0 i j)

/-- Every output of `add_kerr`: metric, inverse, the three derivative
matrices and the clearance. -/
inductive Output
  | metric (i j : Fin 4)
  | inverse (i j : Fin 4)
  | derivative (e : Fin 3) (i j : Fin 4)
  | clearance

def program : Output → GExpr
  | .metric i j => gOut i j
  | .inverse i j => invOut i j
  | .derivative e i j => dOut e i j
  | .clearance => clearance

/-- The WGSL error of every `add_kerr` output, for every input satisfying the
safety conditions of its program. -/
theorem add_kerr_error (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (o : Output) (y : ℝ)
    (hs : (program o).Safe v E) (hy : (program o).Computes w y) :
    |y-(program o).exact v| ≤ (program o).bound v E :=
  error (program o) v w E hw y hs hy

/-- A comparison with an exact threshold agrees in both evaluations when the
compared value is farther from the threshold than its error. -/
theorem flag_agree (exact y t B : ℝ) (he : |y-exact| ≤ B) (hsep : B < |exact-t|) :
    (y < t ↔ exact < t) := by
  constructor
  · intro hyt
    by_contra hn
    rw [not_lt] at hn
    rw [abs_of_nonneg (by linarith)] at hsep
    have := (abs_le.mp he).1
    linarith
  · intro het
    rw [abs_of_neg (by linarith)] at hsep
    have := (abs_le.mp he).2
    linarith

/-! `spin` is scaled into `a = mass*spin/max(1, length(spin)/0.999)`; inputs
`spin` 0–2 and `mass` 3. -/

def spinNorm : GExpr := sqrt (sum3 fun i => mul (input i) (input i))
def spinScale (i : Fin 3) : GExpr :=
  div (mul (input 3) (input i)) (max (c 1) (div spinNorm (c f32_0_999)))

theorem spin_scale_error (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (i : Fin 3) (y : ℝ)
    (hs : (spinScale i).Safe v E) (hy : (spinScale i).Computes w y) :
    |y-(spinScale i).exact v| ≤ (spinScale i).bound v E :=
  error (spinScale i) v w E hw y hs hy

end BlackHole.WgslAddKerr
