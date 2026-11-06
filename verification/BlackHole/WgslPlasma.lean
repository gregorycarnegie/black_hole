module

public import BlackHole.WgslScreen

/-! All-input WGSL error bounds for `sample_plasma` and its helpers in
`geodesic.wesl` (obligation F2), for all four disk models (thin, truncated
hot flow, slim, warped) of a single, non-binary source.

Every builtin follows the WGSL f32 accuracy table: `pow(x, y)` is inherited
from `exp2(y * log2(x))`, `tanh` is the worse of `10⁻⁵` absolute and
`sinh/cosh`, `smoothstep`, `mix`, `normalize`, `length` and `clamp` are
inherited from their defining expressions, and decimal literals are their
binary32 values. Matrix entries `M i j` denote row `i`, column `j`
(`m.M[j][i]` in WGSL), as in `WgslScreen`, so `screen_frame` is reused
directly.

The warped model's `disk_midplane_y` used to take `atan2(pos.z, pos.x)`,
which WGSL leaves unspecified at `pos.z = 0` (`WgslCounterexamples`). It now
computes `sin(φ-γ) = (z cos γ - x sin γ)/ρ` from the arithmetic `sincos`
(`GExpr.sinS`/`cosS`, bounded by `WgslSinCos.sincos_error`), returning `0`
on the axis. `polarization_color` view 2 likewise replaces
`cos(atan2(y,x)+c)` by `(x cos c - y sin c)/|pol.xy|`.

Inputs: `g` 0–15, `inv` 16–31, `p` 32–35, screen 36–39, `pos` 40–42, disk
`r1` 43, `r2` 44, `h_thin` 45, `h_hot` 46, `spin` 47, `isco_r` 48, `r_trunc`
49, camera `frequency_ghz` 50, `faraday_depth` 51, `conversion_depth` 52, and
for the warped model `r_bp` 53, `tilt_deg` 54, `twist_deg` 55. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslPlasma
open Wgsl WgslExpr GExpr WgslScreen

/-! ### Literals (binary32 values) -/

def c (r : ℚ) : GExpr := const r
def L0_4 : ℚ := 13421773/33554432
def L1em4 : ℚ := 13743895/137438953472
def L1em3 : ℚ := 8589935/8589934592
def L0_01 : ℚ := 5368709/536870912
def L0_06 : ℚ := 16106127/268435456
def L0_35 : ℚ := 11744051/33554432
def L0_488 : ℚ := 16374563/33554432
def L0_6 : ℚ := 5033165/8388608
def L0_65 : ℚ := 5452595/8388608
def L0_3 : ℚ := 5033165/16777216
def L0_2126 : ℚ := 891709/4194304
def L0_7152 : ℚ := 11999065/16777216
def L0_0722 : ℚ := 1211315/16777216
def L0_7 : ℚ := 11744051/16777216
def L1em5 : ℚ := 2748779/274877906944
def L0_95 : ℚ := 15938355/16777216
def L0_80 : ℚ := 13421773/16777216
def L0_05 : ℚ := 13421773/268435456
def L0_02 : ℚ := 5368709/268435456
def L0_999 : ℚ := 16760439/16777216
def L1em12 : ℚ := 2305843/2305843009213693952
def L1em20 : ℚ := 1547425/154742504910672534362390528
def L0_1 : ℚ := 13421773/134217728
def L1em8 : ℚ := 11258999/1125899906842624
/-- `PI / 180.0` evaluated in binary32. -/
def LPI_180 : ℚ := 9370165/536870912
def LSQRT3_2 : ℚ := 14529495/16777216

/-! ### Inputs -/

def pos (i : Fin 3) : GExpr := input (40+i)
def r1 : GExpr := input 43
def r2 : GExpr := input 44
def hThin : GExpr := input 45
def hHot : GExpr := input 46
def spin : GExpr := input 47
def isco : GExpr := input 48
def rTrunc : GExpr := input 49
def freq : GExpr := input 50
def faraday : GExpr := input 51
def conversion : GExpr := input 52
def rBp : GExpr := input 53
def tilt : GExpr := input 54
def twist : GExpr := input 55

/-! ### Inherited builtins -/

def clamp (x lo hi : GExpr) : GExpr := min (max x lo) hi
def mix (a b t : GExpr) : GExpr := add (mul a (sub (c 1) t)) (mul b t)
def smoothstep (e0 e1 x : GExpr) : GExpr :=
  let t := clamp (div (sub x e0) (sub e1 e0)) (c 0) (c 1)
  mul (mul t t) (sub (c 3) (mul (c 2) t))
/-- `pow(x, y)` for an exact exponent, inherited from `exp2(y * log2(x))`. -/
def pow (x : GExpr) (y : ℚ) : GExpr := inh (exp2 (mul (c y) (log2 (input 0)))) x
def tanhInh : GExpr :=
  div (mul (sub (exp (input 0)) (exp (neg (input 0)))) (c (1/2)))
    (mul (add (exp (input 0)) (exp (neg (input 0)))) (c (1/2)))
def tanhW (x : GExpr) : GExpr := tanh tanhInh x

theorem tanhInh_exact (t : ℝ) : tanhInh.exact (fun _ => t) = Real.tanh t := by
  simp only [tanhInh,exact,c]
  rw [Real.tanh_eq_sinh_div_cosh,Real.sinh_eq,Real.cosh_eq]
  ring

def dot3 (a b : Fin 3 → GExpr) : GExpr := add (add (mul (a 0) (b 0)) (mul (a 1) (b 1))) (mul (a 2) (b 2))
def dot4 (a b : Fin 4 → GExpr) : GExpr :=
  add (add (add (mul (a 0) (b 0)) (mul (a 1) (b 1))) (mul (a 2) (b 2))) (mul (a 3) (b 3))
def gMul (v : Fin 4 → GExpr) (i : Fin 4) : GExpr := dot4 (fun j => g i j) v
def normalize (v : Fin 3 → GExpr) (i : Fin 3) : GExpr := div (v i) (sqrt (dot3 v v))

/-! ### Disk helpers -/

/-- `kerr_radius(vec3(pos.x,0,pos.z), vec3(0, clamp(spin,-0.999,0.999), 0))`. -/
def diskRadius : GExpr :=
  let x : Fin 3 → GExpr := ![pos 0,c 0,pos 2]
  let a : Fin 3 → GExpr := ![c 0,clamp spin (c (-L0_999)) (c L0_999),c 0]
  let q := sub (dot3 x x) (dot3 a a)
  let ax := dot3 a x
  let root := sqrt (add (mul q q) (mul (mul (c 4) ax) ax))
  let r2 := lt q 0 (div (mul (mul (c 2) ax) ax) (max (sub root q) (c L1em20)))
    (mul (c (1/2)) (add q root))
  sqrt (max r2 (c L1em12))

/-- `disk_midplane_y(r, pos.xz)` for the warped model, without `atan2`:
`sin(φ-γ) = (z cos γ - x sin γ)/ρ`, with the axis returned as `0`. -/
def midplane (r : GExpr) : GExpr :=
  let rbpSafe := max rBp (c (2*L0_1))
  let lnNorm := clamp (div (log (div (max r (c (2*L0_01))) rbpSafe)) (c (1/2))) (c (-10)) (c 10)
  let w := mul (c (1/2)) (add (c 1) (tanhW lnNorm))
  let beta := mul (mul tilt (c LPI_180)) w
  let gamma := mul (mul twist (c LPI_180)) (log (add (c 1) (div r rbpSafe)))
  let rho2 := add (mul (pos 0) (pos 0)) (mul (pos 2) (pos 2))
  lt (neg rho2) 0
    (mul (mul r (sinS beta)) (div (sub (mul (pos 2) (cosS gamma)) (mul (pos 0) (sinS gamma)))
      (sqrt rho2)))
    (c 0)

def hOverR (model : Fin 4) (r : GExpr) : GExpr :=
  if model = 1 then
    let safeR := max r (c (2*L1em3))
    let safeRt := max rTrunc (c (2*L1em3))
    let t := clamp (div (sub (log safeR) (log safeRt)) (c L0_4)) (c (-10)) (c 10)
    let w := mul (c (1/2)) (add (c 1) (tanhW t))
    add (mul w hThin) (mul (sub (c 1) w) hHot)
  else if model = 2 then
    let ratio := div r (max rTrunc (c 1))
    add hThin (div (sub hHot hThin) (add (c 1) (mul ratio ratio)))
  else hThin

def edgeFade (r : GExpr) : GExpr :=
  let width := max (mul (c L0_06) (sub r2 r1)) (c (2*L0_35))
  let inner := smoothstep r1 (add r1 width) r
  let outer := sub (c 1) (smoothstep (sub r2 width) r2 r)
  clamp (mul inner outer) (c 0) (c 1)

def ntTemp (r : GExpr) : GExpr :=
  let sr := sqrt (div isco r)
  let f := max (sub (c 1) sr) (c 0)
  mul (mul sr (sqrt sr)) (sqrt (sqrt f))

def blackbody (t : GExpr) (i : Fin 3) : GExpr :=
  let s := clamp t (c 0) (c 1)
  let c1 : Fin 3 → ℚ := ![L0_05,0,0]
  let c2 : Fin 3 → ℚ := ![1,L0_35,L0_02]
  let c3 : Fin 3 → ℚ := ![1,L0_95,L0_80]
  let c4 : Fin 3 → ℚ := ![L0_65,L0_80,1]
  lt s L0_4 (mix (c (c1 i)) (c (c2 i)) (div s (c L0_4)))
    (lt s (3/4) (mix (c (c2 i)) (c (c3 i)) (div (sub s (c L0_4)) (c L0_35)))
      (mix (c (c3 i)) (c (c4 i)) (div (sub s (c (3/4))) (c (1/4)))))

def hotEmissivity (r : GExpr) : GExpr :=
  let r0 := max isco r1
  pow (clamp (div r0 (max r r0)) (c 0) (c 1)) L0_6

/-! ### `sample_plasma` -/

/-- The twelve `Plasma` fields: rgb 0–2, j 3–6, alpha 7, rho 8–10, energy 11. -/
def mid (model : Fin 4) (r : GExpr) : GExpr := if model = 3 then midplane r else c 0

def body (model : Fin 4) (o : Fin 12) : GExpr :=
  let r := diskRadius
  let hr := hOverR model r
  let height := max (mul hr r) (c L1em4)
  let z := div (sub (pos 1) (mid model r)) height
  let density := div (mul (mul (c L0_4) (exp (mul (mul (c (-1/2)) z) z))) (edgeFade r)) height
  let kk : Fin 4 → GExpr := k
  let omega := div (sub (c 1) (mul (c (1/2)) (clamp (mul hr (c 2)) (c 0) (c 1))))
    (max (add (pow r (3/2)) spin) (c L1em3))
  let tangent : Fin 3 → GExpr := ![pos 2,c 0,neg (pos 0)]
  let fluid0 : Fin 4 → GExpr := ![c 1,mul omega (tangent 0),mul omega (tangent 1),mul omega (tangent 2)]
  let norm := dot4 fluid0 (gMul fluid0)
  let lapse := invsqrt (neg (inv 0 0))
  let fluid : Fin 4 → GExpr := fun i =>
    lt norm (-L1em4) (mul (fluid0 i) (invsqrt (neg norm))) (mul (neg lapse) (inv i 0))
  let energy := max (dot4 p fluid) (c L1em5)
  let redshift := clamp (div (c 1) energy) (c L0_01) (c 20)
  let freqRatio := div (c 230) (max (div freq redshift) (c 1))
  let e1v : Fin 4 → GExpr := Fin.cases (c 0) (frame 0)
  let e2v : Fin 4 → GExpr := Fin.cases (c 0) (frame 1)
  let e1 : Fin 4 → GExpr := fun i => sub (e1v i) (mul (kk i) (div (dot4 e1v (gMul fluid)) energy))
  let e2 : Fin 4 → GExpr := fun i => sub (e2v i) (mul (kk i) (div (dot4 e2v (gMul fluid)) energy))
  let b0 : Fin 4 → GExpr := Fin.cases (c 0) (normalize tangent)
  let b1 : Fin 4 → GExpr := fun i => add (b0 i) (mul (fluid i) (dot4 b0 (gMul fluid)))
  let b : Fin 4 → GExpr := fun i => mul (b1 i) (invsqrt (max (dot4 b1 (gMul b1)) (c L1em12)))
  let bx := dot4 b (gMul e1)
  let by' := dot4 b (gMul e2)
  let bpar := div (neg (dot4 b (gMul kk))) energy
  let perp2 := clamp (add (mul bx bx) (mul by' by')) (c 0) (c 1)
  let evpaDen := max (add (mul bx bx) (mul by' by')) (c L1em12)
  let evpa : Fin 2 → GExpr := ![div (sub (mul by' by') (mul bx bx)) evpaDen,
    div (mul (mul (c (-2)) bx) by') evpaDen]
  let hot := if model = 1 then
      mul (c (1/2)) (sub (c 1) (tanhW (clamp (div (log (div r (max rTrunc (c L1em3)))) (c L0_4))
        (c (-10)) (c 10))))
    else c 0
  let thermal : Fin 3 → GExpr := fun i => mul (sub (c 1) hot) (blackbody (div (ntTemp r) (c L0_488)) i)
  let tint : Fin 3 → ℚ := ![1,L0_65,L0_3]
  let synch : Fin 3 → GExpr := fun i =>
    mul (mul (mul (mul hot (hotEmissivity r)) perp2) freqRatio) (c (tint i))
  let boost := mul (mul redshift redshift) redshift
  let rgb : Fin 3 → GExpr := fun i => mul (mul density boost) (add (thermal i) (synch i))
  let lum : Fin 3 → ℚ := ![L0_2126,L0_7152,L0_0722]
  let intensity := dot3 rgb (fun i => c (lum i))
  let synchI := mul (mul density boost) (dot3 synch (fun i => c (lum i)))
  let rotation := mul (mul (mul (mul (mul (c 2) faraday) density) bpar) freqRatio) freqRatio
  let conv := mul (mul (mul conversion density) perp2) (pow freqRatio 3)
  match o with
  | 0 => rgb 0 | 1 => rgb 1 | 2 => rgb 2
  | 3 => intensity
  | 4 => mul (mul (c (3/4)) synchI) (evpa 0)
  | 5 => mul (mul (c (3/4)) synchI) (evpa 1)
  | 6 => c 0
  | 7 => mul (c L0_7) density
  | 8 => mul conv (evpa 0)
  | 9 => mul conv (evpa 1)
  | 10 => rotation
  | 11 => energy

/-- The early returns: outside `(r1, r2)` or with `|z| ≥ 4`, every field is zero. -/
def plasma (model : Fin 4) (o : Fin 12) : GExpr :=
  let r := diskRadius
  let z := div (sub (pos 1) (mid model r)) (max (mul (hOverR model r) r) (c L1em4))
  lt2 r1 r (lt2 r r2 (lt (abs z) 4 (body model o) (c 0)) (c 0)) (c 0)

theorem sample_plasma_error (model : Fin 4) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i)
    (o : Fin 12) (y : ℝ) (hs : (plasma model o).Safe v E) (hy : (plasma model o).Computes w y) :
    |y-(plasma model o).exact v| ≤ (plasma model o).bound v E :=
  error (plasma model o) v w E hw y hs hy

/-! ### Display kernels -/

/-- `polarization_color` view 2 channel `k` (inputs: Stokes `I,Q,U,V` 0–3), with
`cos(atan2(y,x)+c) = (x cos c - y sin c)/|pol.xy|` in place of `atan2`/`cos`. -/
def polarizationHue (k : Fin 3) : GExpr :=
  let pol (i : Fin 3) : GExpr := clamp (div (input (i+1)) (input 0)) (c (-1)) (c 1)
  let rho2 := add (mul (pol 0) (pol 0)) (mul (pol 1) (pol 1))
  let rho := sqrt rho2
  let ux := div (pol 0) rho
  let uy := div (pol 1) rho
  let comp : Fin 3 → GExpr := ![ux,add (mul (c (-1/2)) ux) (mul (c LSQRT3_2) uy),
    sub (mul (c (-1/2)) ux) (mul (c LSQRT3_2) uy)]
  lt (neg (input 0)) (-L1em8)
    (lt (neg rho2) 0 (mul (add (c (1/2)) (mul (c (1/2)) (comp k))) (clamp rho (c 0) (c 1))) (c 0))
    (c 0)

theorem polarization_hue_error (k : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (y : ℝ)
    (hs : (polarizationHue k).Safe v E) (hy : (polarizationHue k).Computes w y) :
    |y-(polarizationHue k).exact v| ≤ (polarizationHue k).bound v E :=
  error (polarizationHue k) v w E hw y hs hy

theorem midplane_error (r : GExpr) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (y : ℝ)
    (hs : (midplane r).Safe v E) (hy : (midplane r).Computes w y) :
    |y-(midplane r).exact v| ≤ (midplane r).bound v E :=
  error (midplane r) v w E hw y hs hy

/-- `tonemap`: clamped ACES polynomial ratio, per channel (input 0). -/
def tonemap : GExpr :=
  let x := clamp (input 0) (c 0) (c 10000)
  clamp (div (mul x (add (mul (c (10527703/4194304)) x) (c (16106127/536870912))))
    (add (mul x (add (mul (c (10192159/4194304)) x) (c (9898557/16777216)))) (c (9395241/67108864))))
    (c 0) (c 1)

theorem tonemap_error (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i) (y : ℝ)
    (hs : tonemap.Safe v E) (hy : tonemap.Computes w y) :
    |y-tonemap.exact v| ≤ tonemap.bound v E :=
  error tonemap v w E hw y hs hy

/-- `heatmap_color` channel `i`: `clamp(t*3, 0, 1)` for `i = 0`, else
`clamp(t*3 - i, 0, 1)` (input 0). -/
def heatmap (i : Fin 3) : GExpr :=
  clamp (if i = 0 then mul (input 0) (c 3) else sub (mul (input 0) (c 3)) (c (i:ℚ))) (c 0) (c 1)

theorem heatmap_error (i : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (y : ℝ)
    (hs : (heatmap i).Safe v E) (hy : (heatmap i).Computes w y) :
    |y-(heatmap i).exact v| ≤ (heatmap i).bound v E :=
  error (heatmap i) v w E hw y hs hy

/-! `intersect_objects_segment` for one object: `start` 0–2, `end` 3–5, centre
6–8, radius 9. The closest-point parameter is a running-bounded program; the
hit decision `dot(offset, offset) <= radius*radius` agrees in both evaluations
whenever `radius² - |offset|²` is farther from zero than its error
(`WgslAddKerr.flag_agree`), and the reported colour, centre and radius are
copied inputs. -/

def segStart (i : Fin 3) : GExpr := input i
def segEnd (i : Fin 3) : GExpr := input (3+i)
def centre (i : Fin 3) : GExpr := input (6+i)
def segment (i : Fin 3) : GExpr := sub (segEnd i) (segStart i)
def segParam : GExpr :=
  clamp (div (dot3 (fun i => sub (centre i) (segStart i)) segment)
    (max (dot3 segment segment) (c L1em12))) (c 0) (c 1)
def offset (i : Fin 3) : GExpr := sub (add (segStart i) (mul (segment i) segParam)) (centre i)
def hitMargin : GExpr := sub (mul (input 9) (input 9)) (dot3 offset offset)

theorem hit_margin_error (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (y : ℝ)
    (hs : hitMargin.Safe v E) (hy : hitMargin.Computes w y) :
    |y-hitMargin.exact v| ≤ hitMargin.bound v E :=
  error hitMargin v w E hw y hs hy

end BlackHole.WgslPlasma
