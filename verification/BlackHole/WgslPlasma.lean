module

public import BlackHole.WgslScreen

/-! All-input WGSL error bounds for `sample_plasma` and its helpers in
`geodesic.wesl` (obligation F2), for disk models 0 (thin), 1 (truncated hot
flow) and 2 (slim) of a single, non-binary source.

Every builtin follows the WGSL f32 accuracy table: `pow(x, y)` is inherited
from `exp2(y * log2(x))`, `tanh` is the worse of `10⁻⁵` absolute and
`sinh/cosh`, `smoothstep`, `mix`, `normalize`, `length` and `clamp` are
inherited from their defining expressions, and decimal literals are their
binary32 values. Matrix entries `M i j` denote row `i`, column `j`
(`m.M[j][i]` in WGSL), as in `WgslScreen`, so `screen_frame` is reused
directly. The `atan2` argument of `disk_midplane_y` is computed but unused
for these models.

The warped model (3) uses `atan2(pos.z, pos.x)`. WGSL defines `atan2(y, x)`
only for `|x| ∈ [2⁻¹²⁶, 2¹²⁶]` and normal `y`, so for `pos.z = 0` or tiny
`pos.x` its value is unconstrained and no all-input bound can hold
(`WgslCounterexamples`).

Inputs: `g` 0–15, `inv` 16–31, `p` 32–35, screen 36–39, `pos` 40–42, disk
`r1` 43, `r2` 44, `h_thin` 45, `h_hot` 46, `spin` 47, `isco_r` 48, `r_trunc`
49, camera `frequency_ghz` 50, `faraday_depth` 51, `conversion_depth` 52. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslPlasma
open Wgsl WgslExpr GExpr WgslScreen

/-! ### Literals (binary32 values) -/

def c (r : ℝ) : GExpr := const r
def L0_4 : ℝ := 13421773/33554432
def L1em4 : ℝ := 13743895/137438953472
def L1em3 : ℝ := 8589935/8589934592
def L0_01 : ℝ := 5368709/536870912
def L0_06 : ℝ := 16106127/268435456
def L0_35 : ℝ := 11744051/33554432
def L0_488 : ℝ := 16374563/33554432
def L0_6 : ℝ := 5033165/8388608
def L0_65 : ℝ := 5452595/8388608
def L0_3 : ℝ := 5033165/16777216
def L0_2126 : ℝ := 891709/4194304
def L0_7152 : ℝ := 11999065/16777216
def L0_0722 : ℝ := 1211315/16777216
def L0_7 : ℝ := 11744051/16777216
def L1em5 : ℝ := 2748779/274877906944
def L0_95 : ℝ := 15938355/16777216
def L0_80 : ℝ := 13421773/16777216
def L0_05 : ℝ := 13421773/268435456
def L0_02 : ℝ := 5368709/268435456
def L0_999 : ℝ := 16760439/16777216
def L1em12 : ℝ := 2305843/2305843009213693952
def L1em20 : ℝ := 1547425/154742504910672534362390528

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

/-! ### Inherited builtins -/

def clamp (x lo hi : GExpr) : GExpr := min (max x lo) hi
def mix (a b t : GExpr) : GExpr := add (mul a (sub (c 1) t)) (mul b t)
def smoothstep (e0 e1 x : GExpr) : GExpr :=
  let t := clamp (div (sub x e0) (sub e1 e0)) (c 0) (c 1)
  mul (mul t t) (sub (c 3) (mul (c 2) t))
/-- `pow(x, y)` for an exact exponent, inherited from `exp2(y * log2(x))`. -/
def pow (x : GExpr) (y : ℝ) : GExpr := inh (exp2 (mul (c y) (log2 (input 0)))) x
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

def hOverR (model : Fin 3) (r : GExpr) : GExpr :=
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
  let c1 : Fin 3 → ℝ := ![L0_05,0,0]
  let c2 : Fin 3 → ℝ := ![1,L0_35,L0_02]
  let c3 : Fin 3 → ℝ := ![1,L0_95,L0_80]
  let c4 : Fin 3 → ℝ := ![L0_65,L0_80,1]
  lt s L0_4 (mix (c (c1 i)) (c (c2 i)) (div s (c L0_4)))
    (lt s (3/4) (mix (c (c2 i)) (c (c3 i)) (div (sub s (c L0_4)) (c L0_35)))
      (mix (c (c3 i)) (c (c4 i)) (div (sub s (c (3/4))) (c (1/4)))))

def hotEmissivity (r : GExpr) : GExpr :=
  let r0 := max isco r1
  pow (clamp (div r0 (max r r0)) (c 0) (c 1)) L0_6

/-! ### `sample_plasma` -/

/-- The twelve `Plasma` fields: rgb 0–2, j 3–6, alpha 7, rho 8–10, energy 11. -/
def body (model : Fin 3) (o : Fin 12) : GExpr :=
  let r := diskRadius
  let hr := hOverR model r
  let height := max (mul hr r) (c L1em4)
  let z := div (pos 1) height
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
  let tint : Fin 3 → ℝ := ![1,L0_65,L0_3]
  let synch : Fin 3 → GExpr := fun i =>
    mul (mul (mul (mul hot (hotEmissivity r)) perp2) freqRatio) (c (tint i))
  let boost := mul (mul redshift redshift) redshift
  let rgb : Fin 3 → GExpr := fun i => mul (mul density boost) (add (thermal i) (synch i))
  let lum : Fin 3 → ℝ := ![L0_2126,L0_7152,L0_0722]
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
def plasma (model : Fin 3) (o : Fin 12) : GExpr :=
  let r := diskRadius
  let z := div (pos 1) (max (mul (hOverR model r) r) (c L1em4))
  lt2 r1 r (lt2 r r2 (lt (abs z) 4 (body model o) (c 0)) (c 0)) (c 0)

theorem sample_plasma_error (model : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i)
    (o : Fin 12) (y : ℝ) (hs : (plasma model o).Safe v E) (hy : (plasma model o).Computes w y) :
    |y-(plasma model o).exact v| ≤ (plasma model o).bound v E :=
  error (plasma model o) v w E hw y hs hy

/-! ### Display kernels -/

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

/-- `heatmap_color` channel `i`: `clamp(t*3 - i, 0, 1)` (input 0). -/
def heatmap (i : Fin 3) : GExpr := clamp (sub (mul (input 0) (c 3)) (c (i:ℝ))) (c 0) (c 1)

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
