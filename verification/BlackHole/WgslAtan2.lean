module

public import BlackHole.WgslPoly
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds

/-! The arithmetic `atan2_arith` in `geodesic.wesl` (obligation F2).

```
fn atan_poly(u: f32) -> f32 { /* u*(1 + u2*(-1/3 + ... + u2*(1/25))) */ }
fn atan2_arith(y: f32, x: f32) -> f32 {
    let ax = abs(x); let ay = abs(y); let hi = max(ax, ay);
    if hi == 0.0 { return 0.0; }
    let t = min(ax, ay) / hi;
    var a = atan_poly(t);
    if t > TAN_PI_8 { a = 0.25*PI + atan_poly((t-1.0)/(t+1.0)); }
    if ay > ax { a = 0.5*PI - a; }
    if x < 0.0 { a = PI - a; }
    if y < 0.0 { a = -a; }
    return a;
}
```

It replaces builtin `atan2` and `acos`, whose WGSL accuracy is unspecified
for `y = 0` or `|x| < 2⁻¹²⁶`. `octant_arg` shows the octant steps map
`arctan(min/max)` exactly onto `Complex.arg`; `arctan_tail` bounds the
degree-25 Taylor truncation; `atan2_arith_error` bounds the whole function
under the WGSL model by `128u` absolute. The branch on the computed `t`
needs no separation condition, because both branches approximate the same
`arctan(t)`. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslAtan2
open Wgsl WgslPoly Real

/-! ### Exact octant reduction -/

def octant (y x a : ℝ) : ℝ :=
  let a1 := if |x| < |y| then π/2-a else a
  let a2 := if x < 0 then π-a1 else a1
  if y < 0 then -a2 else a2

lemma arctan_lip (a b : ℝ) : |arctan a-arctan b| ≤ |a-b| := by
  have hb (t : ℝ) : ‖1/(1+t^2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (by positivity),div_le_one (by positivity)]
    nlinarith [sq_nonneg t]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := arctan)
    (fun t _ => (hasDerivAt_arctan t).hasDerivWithinAt) (fun t _ => hb t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

lemma norm_mk (x y : ℝ) : ‖(⟨x,y⟩ : ℂ)‖ = √(x^2+y^2) := by
  rw [Complex.norm_def,Complex.normSq_mk]; ring_nf

lemma arcsin_div_norm {u v : ℝ} (hu : 0 < u) : arcsin (v/√(u^2+v^2)) = arctan (v/u) := by
  rw [arctan_eq_arcsin]
  congr 1
  have hs : √(1+(v/u)^2) = √(u^2+v^2)/u := by
    rw [show 1+(v/u)^2 = (u^2+v^2)/u^2 by field_simp,Real.sqrt_div' _ (sq_nonneg u),
      Real.sqrt_sq hu.le]
  have hpos : 0 < √(u^2+v^2) := Real.sqrt_pos.mpr (by positivity)
  rw [hs]
  field_simp

/-- The octant formula with `A = arctan(|y|/|x|)` for `x ≠ 0`. -/
lemma core (x y : ℝ) (hx : x ≠ 0) :
    (if y < 0 then -(if x < 0 then π-arctan (|y|/|x|) else arctan (|y|/|x|))
      else (if x < 0 then π-arctan (|y|/|x|) else arctan (|y|/|x|))) = Complex.arg ⟨x,y⟩ := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- x < 0
    have hre : (⟨x,y⟩ : ℂ).re < 0 := hneg
    have hu : 0 < -x := by linarith
    have hb : arcsin (-y/√((-x)^2+(-y)^2)) = arctan (y/x) := by
      rw [arcsin_div_norm hu]; congr 1; field_simp
    have hn : √((-x)^2+(-y)^2) = ‖(⟨x,y⟩ : ℂ)‖ := by rw [norm_mk]; ring_nf
    rw [hn] at hb
    simp only [hneg,↓reduceIte]
    by_cases hy : y < 0
    · rw [Complex.arg_of_re_neg_of_im_neg hre hy]
      simp only [hy,↓reduceIte,Complex.neg_im]
      rw [show -y/‖(⟨x,y⟩ : ℂ)‖ = -y/‖(⟨x,y⟩ : ℂ)‖ from rfl,hb,abs_of_neg hy,abs_of_neg hneg,
        show (-y)/(-x) = y/x by ring]
      ring
    · rw [not_lt] at hy
      rw [Complex.arg_of_re_neg_of_im_nonneg hre hy]
      simp only [show ¬ y < 0 from not_lt.mpr hy,↓reduceIte,Complex.neg_im]
      rw [hb,abs_of_nonneg hy,abs_of_neg hneg,show y/(-x) = -(y/x) by ring,arctan_neg]
      ring
  · -- x > 0
    have hre : 0 ≤ (⟨x,y⟩ : ℂ).re := hpos.le
    have hb : arcsin (y/√(x^2+y^2)) = arctan (y/x) := arcsin_div_norm hpos
    rw [← norm_mk] at hb
    rw [Complex.arg_of_re_nonneg hre]
    simp only [show ¬ x < 0 from not_lt.mpr hpos.le,↓reduceIte]
    change _ = arcsin (y/‖(⟨x,y⟩ : ℂ)‖)
    rw [hb,abs_of_pos hpos]
    by_cases hy : y < 0
    · simp only [hy,↓reduceIte]; rw [abs_of_neg hy,show -y/x = -(y/x) by ring,arctan_neg]; ring
    · simp only [hy,↓reduceIte]; rw [abs_of_nonneg (not_lt.mp hy)]

/-- The program's octant steps turn `arctan(min/max)` into the exact argument. -/
theorem octant_arg (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    octant y x (arctan (min |x| |y|/max |x| |y|)) = Complex.arg ⟨x,y⟩ := by
  unfold octant
  by_cases hxy : |x| < |y|
  · simp only [hxy,↓reduceIte]
    rw [min_eq_left hxy.le,max_eq_right hxy.le]
    have hy0 : 0 < |y| := lt_of_le_of_lt (abs_nonneg x) hxy
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := abs_pos.mp hy0
      simp only [abs_zero,zero_div,arctan_zero,sub_zero,lt_irrefl,↓reduceIte]
      have hre : 0 ≤ (⟨0,y⟩ : ℂ).re := le_rfl
      rw [Complex.arg_of_re_nonneg hre,norm_mk]
      change _ = arcsin (y/√(0^2+y^2))
      rw [show (0:ℝ)^2+y^2 = y^2 by ring,Real.sqrt_sq_eq_abs]
      by_cases hneg : y < 0
      · simp only [hneg,↓reduceIte]; rw [abs_of_neg hneg,show y/(-y) = -1 by field_simp,arcsin_neg_one]
      · simp only [hneg,↓reduceIte]
        rw [abs_of_pos (lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hy)),div_self hy,arcsin_one]
    · have hx0 : 0 < |x| := abs_pos.mpr hx
      have hinv : π/2-arctan (|x|/|y|) = arctan (|y|/|x|) := by
        rw [← arctan_inv_of_pos (div_pos hx0 hy0),inv_div]
      rw [hinv]
      exact core x y hx
  · simp only [hxy,↓reduceIte]
    rw [not_lt] at hxy
    rw [min_eq_right hxy,max_eq_left hxy]
    have hx : x ≠ 0 := by
      rintro rfl
      rcases h with h | h
      · exact h rfl
      · exact h (abs_eq_zero.mp (le_antisymm (by simpa using hxy) (abs_nonneg y)))
    exact core x y hx

/-! ### Taylor truncation -/

def poly (u : ℝ) : ℝ := ∑ n ∈ Finset.range 13, (-1:ℝ)^n*u^(2*n+1)/(2*n+1)

/-- The degree-25 odd Taylor polynomial of `arctan` on `|u| ≤ 1/2`. -/
theorem arctan_tail (u : ℝ) (hu : |u| ≤ 1/2) :
    |arctan u-poly u| ≤ |u|^27/(27*(1-u^2)) := by
  have h1 : ‖u‖ < 1 := by rw [Real.norm_eq_abs]; linarith
  have hs := Real.hasSum_arctan h1
  set f : ℕ → ℝ := fun n => (-1)^n*u^(2*n+1)/↑(2*n+1)
  have hsplit := hs.summable.sum_add_tsum_nat_add 13
  have hu2 : u^2 ≤ 1/4 := by nlinarith [abs_nonneg u, sq_abs u]
  have hgeom : Summable (fun i : ℕ => |u|^27/27*(u^2)^i) :=
    (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hle (i : ℕ) : ‖f (i+13)‖ ≤ |u|^27/27*(u^2)^i := by
    simp only [f,Real.norm_eq_abs,abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    rw [abs_of_pos (by positivity : (0:ℝ) < ↑(2*(i+13)+1))]
    have hp : |u|^(2*(i+13)+1) = |u|^27*(u^2)^i := by
      rw [← sq_abs u,← pow_mul,← pow_add]; ring_nf
    rw [hp,div_le_iff₀ (by positivity)]
    have : (27:ℝ) ≤ ↑(2*(i+13)+1) := by push_cast; linarith
    have hnn : 0 ≤ |u|^27*(u^2)^i := by positivity
    calc |u|^27*(u^2)^i = |u|^27/27*(u^2)^i*27 := by ring
      _ ≤ _ := by gcongr
  have htail : |∑' i, f (i+13)| ≤ |u|^27/(27*(1-u^2)) := by
    have hsum : Summable (fun i => f (i+13)) := (summable_nat_add_iff 13).mpr hs.summable
    calc |∑' i, f (i+13)| ≤ ∑' i, ‖f (i+13)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' i, |u|^27/27*(u^2)^i := hsum.norm.tsum_le_tsum hle hgeom
      _ = |u|^27/(27*(1-u^2)) := by
          rw [tsum_mul_left,tsum_geometric_of_lt_one (by positivity) (by linarith)]
          field_simp
  have heq : arctan u-poly u = ∑' i, f (i+13) := by
    rw [← hs.tsum_eq,← hsplit]
    simp only [poly,f]
    push_cast
    ring
  rw [heq]; exact htail

/-! ### Floating-point evaluation -/

/-- The binary32 coefficients the shader uses (its `±1.0/(2k+1)` literals). -/
def cfs : List ℚ := [1, -11184811/33554432, 13421773/67108864, -9586981/67108864,
  14913081/134217728, -3050403/33554432, 10324441/134217728, -8947849/134217728,
  15790321/268435456, -7064091/134217728, 12782641/268435456, -11671107/268435456,
  5368709/134217728]
def cf (k : ℕ) : ℝ := ((cfs.getD k 0 : ℚ) : ℝ)

/-- `f32(π)`. -/
def PIf : ℝ := 13176795/4194304
/-- `f32(tan(π/8))`. -/
def TANf : ℝ := 13898701/33554432

open PExpr in
def u2 : PExpr := mul (input 0) (input 0)

open PExpr in
def hornerE : List ℝ → PExpr
  | [] => const 0
  | [c] => const c
  | c :: cs => add (const c) (mul u2 (hornerE cs))

open PExpr in
/-- `atan_poly(u)`, reading `u` as input 0. -/
def polyE : PExpr :=
  mul (input 0) (add (const 1) (mul u2 (hornerE [cf 1,cf 2,cf 3,cf 4,cf 5,cf 6,cf 7,cf 8,
    cf 9,cf 10,cf 11,cf 12])))

/-- The polynomial the shader evaluates, with its binary32 coefficients. -/
def p32 (u : ℝ) : ℝ := ∑ k ∈ Finset.range 13, cf k*u^(2*k+1)

theorem polyE_exact (v : ℕ → ℝ) : polyE.exact v = p32 (v 0) := by
  simp only [polyE,hornerE,u2,PExpr.exact,p32,Finset.sum_range_succ,Finset.sum_range_zero]
  have h0 : cf 0 = 1 := by norm_num [cf,cfs]
  rw [h0]
  ring

theorem polyE_ops : polyE.ops (fun _ => 0) = 37 := by
  simp [polyE,hornerE,u2,PExpr.ops]

lemma Γ37 : Γ 37 ≤ 186*u := by
  have hU : U = 5*u := rfl
  have hu : u = 1/2^24 := rfl
  have h : ((37:ℕ):ℝ)*U < 1 := by rw [hU,hu]; norm_num
  refine (Γ_le 37 h).trans ?_
  rw [hU,hu]; norm_num

lemma absEval_le (b : ℝ) (hb : b = 4145/10000) :
    polyE.absEval (fun _ => b) ≤ 45/100 := by
  have he : η/U = (1/2^126)/(5*(1/2^24)) := rfl
  subst hb
  simp only [polyE,hornerE,u2,PExpr.absEval,he,cf,cfs]
  norm_num

lemma coeff_error (v : ℝ) (hv : |v| ≤ 1) : |p32 v-poly v| ≤ u := by
  have heq : p32 v-poly v = ∑ k ∈ Finset.range 13, (cf k-(-1:ℝ)^k/(2*k+1))*v^(2*k+1) := by
    simp only [p32,poly,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq]
  have hterm (k : ℕ) : |(cf k-(-1:ℝ)^k/(2*k+1))*v^(2*k+1)| ≤ |cf k-(-1:ℝ)^k/(2*k+1)| := by
    rw [abs_mul,abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hv)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hterm k).trans ?_)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,cf,cfs]
  norm_num [u]

lemma pi_close : 0 < PIf-π ∧ PIf-π ≤ 151/100*u := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · unfold PIf; norm_num at h2 ⊢; linarith
  · unfold PIf u; norm_num at h1 ⊢; linarith

/-- The polynomial's whole error against `arctan`, for a computed argument
within `0.4145`. -/
theorem poly_vs_arctan (uu p : ℝ) (huu : |uu| ≤ 4145/10000) (hp : polyE.Computes (fun _ => uu) p) :
    |p-arctan uu| ≤ 85*u+1/10^10 := by
  have hr := (PExpr.error (fun _ => uu) (fun _ => uu) (fun _ => 4145/10000) (fun _ => 0)
    (fun _ => huu) (fun _ => by simp [Γ]) polyE p (by simp [polyE,hornerE,u2,PExpr.DivcOk]) hp)
  rw [polyE_exact,polyE_ops] at hr
  have hA := absEval_le _ rfl
  have hround : |p-p32 uu| ≤ 186*u*(45/100) :=
    hr.2.trans (mul_le_mul Γ37 hA ((abs_nonneg _).trans hr.1) (by unfold u; norm_num))
  have hc := coeff_error uu (by linarith)
  have ht := arctan_tail uu (by linarith)
  have htail : |uu|^27/(27*(1-uu^2)) ≤ 1/10^10 := by
    have hsq : uu^2 ≤ (4145/10000)^2 := by rw [← sq_abs]; gcongr
    have hpow : |uu|^27 ≤ (4145/10000)^27 := pow_le_pow_left₀ (abs_nonneg _) huu 27
    rw [div_le_iff₀ (by nlinarith)]
    calc |uu|^27 ≤ (4145/10000)^27 := hpow
      _ ≤ 1/10^10*(27*(1-(4145/10000)^2)) := by norm_num
      _ ≤ 1/10^10*(27*(1-uu^2)) := by gcongr
  have hu : 0 < u := u_pos
  calc |p-arctan uu| ≤ |p-p32 uu|+|p32 uu-poly uu|+|poly uu-arctan uu| := by
        have := abs_sub_le p (p32 uu) (arctan uu)
        have := abs_sub_le (p32 uu) (poly uu) (arctan uu)
        linarith
    _ ≤ 186*u*(45/100)+u+1/10^10 := by
        rw [abs_sub_comm (poly uu)] at *
        linarith [ht.trans htail]
    _ ≤ 85*u+1/10^10 := by nlinarith

set_option maxHeartbeats 8000000 in
/-- The WGSL error of `atan2_arith`: at most `128u` absolute, for every pair of
binary32 inputs with `max(|x|,|y|)` in the WGSL division range. -/
theorem atan2_arith_error (x y : ℝ) (hnz : x ≠ 0 ∨ y ≠ 0)
    (hlo : 1/2^126 ≤ max |x| |y|) (hhi : max |x| |y| ≤ 2^126)
    (t : ℝ) (ht : DivSpec (min |x| |y|) (max |x| |y|) t)
    (a : ℝ) (ha : (¬ TANf < t ∧ polyE.Computes (fun _ => t) a) ∨
      (TANf < t ∧ ∃ dm dp uu p q, Rnd (t-1) dm ∧ Rnd (t+1) dp ∧ DivSpec dm dp uu ∧
        polyE.Computes (fun _ => uu) p ∧ Rnd (1/4*PIf) q ∧ Rnd (q+p) a))
    (a1 : ℝ) (h1 : (|x| < |y| ∧ ∃ hp, Rnd (1/2*PIf) hp ∧ Rnd (hp-a) a1) ∨ (¬ |x| < |y| ∧ a1 = a))
    (a2 : ℝ) (h2 : (x < 0 ∧ Rnd (PIf-a1) a2) ∨ (¬ x < 0 ∧ a2 = a1))
    (r : ℝ) (hr : r = if y < 0 then -a2 else a2) :
    |r-Complex.arg ⟨x,y⟩| ≤ 128*u := by
  have hu : u = 1/2^24 := rfl
  have hη : η = 1/2^126 := rfl
  have hu0 : 0 < u := u_pos
  have hη0 : 0 < η := η_pos
  have hηu : η ≤ u/2^100 := by rw [hu,hη]; norm_num
  set τ := min |x| |y|/max |x| |y| with hτ
  have hmax : 0 < max |x| |y| := lt_of_lt_of_le (by norm_num) hlo
  have hτ0 : 0 ≤ τ := div_nonneg (le_min (abs_nonneg _) (abs_nonneg _)) hmax.le
  have hτ1 : τ ≤ 1 := (div_le_one hmax).mpr (min_le_max)
  have ht := ht ⟨by rwa [abs_of_pos hmax],by rwa [abs_of_pos hmax]⟩
  have htτ : |t-τ| ≤ 5*u+η := by
    unfold Wgsl.Div at ht
    rw [abs_of_nonneg hτ0] at ht
    nlinarith
  have htτ' := abs_le.mp htτ
  -- The angle before the octant steps.
  have hA : |a-arctan τ| ≤ 100*u := by
    rcases ha with ⟨hn,hp⟩ | ⟨hgt,dm,dp,uu,p,q,hdm,hdp,huu,hp,hq,hsum⟩
    · have htle : t ≤ TANf := not_lt.mp hn
      have habs : |t| ≤ 4145/10000 := by
        rw [abs_le]; constructor
        · nlinarith
        · unfold TANf at htle; linarith
      have := poly_vs_arctan t a habs hp
      have hl := arctan_lip t τ
      calc |a-arctan τ| ≤ |a-arctan t|+|arctan t-arctan τ| := abs_sub_le _ _ _
        _ ≤ 85*u+1/10^10+(5*u+η) := by linarith
        _ ≤ 100*u := by rw [hu] at *; rw [hη]; norm_num
    · have hTt : 4142/10000 < t := by unfold TANf at hgt; linarith
      have hτlo : 41/100 < τ := by nlinarith
      set us := (τ-1)/(τ+1) with hus
      have hτp : 0 < τ+1 := by linarith
      have htp : 141/100 < t+1 := by linarith
      have htu : t ≤ 1+6*u := by nlinarith
      -- exact reduction identity
      have hid : arctan τ = π/4+arctan us := by
        rw [← arctan_one,arctan_add (by rw [one_mul]; rw [hus,div_lt_one hτp]; linarith)]
        congr 1; rw [hus]; field_simp; ring
      have husb : |us| ≤ 4143/10000 := by
        rw [hus,abs_div,abs_of_pos hτp,div_le_iff₀ hτp,abs_of_nonpos (by linarith)]
        linarith
      -- computed reduction
      unfold Rnd at hdm hdp
      have hdm' := abs_le.mp hdm
      have hdp' := abs_le.mp hdp
      have hdm1 : |dm-(t-1)| ≤ 6/10*u+η := by
        refine hdm.trans ?_
        have : |t-1| ≤ 6/10 := by rw [abs_le]; constructor <;> nlinarith
        nlinarith
      have hdp1 : |dp-(t+1)| ≤ 21/10*u+η := by
        refine hdp.trans ?_
        have : |t+1| ≤ 21/10 := by rw [abs_le]; constructor <;> nlinarith
        nlinarith
      have hdppos : 14/10 < dp := by have := (abs_le.mp hdp1).1; nlinarith
      have hdp2 : dp ≤ 22/10 := by have := (abs_le.mp hdp1).2; nlinarith
      have huu := huu ⟨by rw [abs_of_pos (by linarith)]; norm_num; linarith,
        by rw [abs_of_pos (by linarith)]; linarith⟩
      unfold Wgsl.Div at huu
      have hus7 : u ≤ 1/10^7 := by rw [hu]; norm_num
      have ht1 : |t-1| ≤ 6/10 := by rw [abs_le]; constructor <;> nlinarith
      have ht2 : |t+1| ≤ 21/10 := by rw [abs_le]; constructor <;> nlinarith
      have hq1 : |dm/dp-(t-1)/(t+1)| ≤ 2*u+η := by
        have hnum : |dm*(t+1)-dp*(t-1)| ≤ 3*u+3*η := by
          rw [show dm*(t+1)-dp*(t-1) = (dm-(t-1))*(t+1)-(t-1)*(dp-(t+1)) by ring]
          calc _ ≤ |(dm-(t-1))*(t+1)|+|(t-1)*(dp-(t+1))| := abs_sub _ _
            _ = |dm-(t-1)| *|t+1|+|t-1| *|dp-(t+1)| := by rw [abs_mul,abs_mul]
            _ ≤ (6/10*u+η)*(21/10)+6/10*(21/10*u+η) := by gcongr
            _ ≤ 3*u+3*η := by nlinarith
        have hden : 197/100 ≤ dp*(t+1) := by nlinarith
        rw [div_sub_div _ _ (by linarith) (by linarith),abs_div,
          abs_of_pos (by linarith : (0:ℝ) < dp*(t+1)),div_le_iff₀ (by linarith)]
        have hm : (2*u+η)*(197/100) ≤ (2*u+η)*(dp*(t+1)) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
        linarith
      have hq2 : |(t-1)/(t+1)-us| ≤ 6*u+η := by
        have hden : 198/100 ≤ (t+1)*(τ+1) := by nlinarith
        rw [hus,div_sub_div _ _ (by linarith) (by linarith),abs_div,
          abs_of_pos (by linarith : (0:ℝ) < (t+1)*(τ+1)),div_le_iff₀ (by linarith)]
        rw [show (t-1)*(τ+1)-(t+1)*(τ-1) = 2*(t-τ) by ring,abs_mul,abs_two]
        nlinarith
      have hqabs : |dm/dp| ≤ 42/100 := by
        have := abs_sub_abs_le_abs_sub (dm/dp) us
        have := abs_sub_le (dm/dp) ((t-1)/(t+1)) us
        rw [hu] at *; rw [hη] at *; nlinarith
      have huus : |uu-us| ≤ 11*u := by
        have := abs_sub_le uu (dm/dp) us
        have := abs_sub_le (dm/dp) ((t-1)/(t+1)) us
        have h3 : |uu-dm/dp| ≤ 5*u*(42/100)+η := huu.trans (by nlinarith)
        linarith
      have huub : |uu| ≤ 4145/10000 := by
        have := abs_sub_abs_le_abs_sub uu us
        rw [hu] at huus; linarith
      have hpoly := poly_vs_arctan uu p huub hp
      have hl := arctan_lip uu us
      unfold Rnd at hq hsum
      have hpi := pi_close
      have hq' : |q-π/4| ≤ 13/10*u+η := by
        have : |q-π/4| ≤ |q-1/4*PIf|+|1/4*PIf-π/4| := abs_sub_le _ _ _
        have h2 : |1/4*PIf-π/4| ≤ 38/100*u := by
          rw [abs_le]; constructor <;> nlinarith
        have h3 : |q-1/4*PIf| ≤ 8/10*u+η := hq.trans (by unfold PIf; rw [abs_of_pos (by norm_num)]; nlinarith)
        linarith
      have hqp : |q+p| ≤ 13/10 := by
        have hpa := abs_sub_abs_le_abs_sub p (arctan uu)
        have harc : |arctan uu| ≤ |uu| := by have := arctan_lip uu 0; simpa using this
        have hpi4 : |π/4| ≤ 79/100 := by
          rw [abs_of_pos (by positivity)]; linarith [Real.pi_lt_d2]
        have hqa := abs_sub_abs_le_abs_sub q (π/4)
        have hq0 : |q| ≤ 80/100 := by linarith
        have hp0 : |p| ≤ 42/100 := by linarith
        linarith [abs_add_le q p]
      calc |a-arctan τ| = |a-(q+p)+(q-π/4)+(p-arctan uu)+(arctan uu-arctan us)| := by
            rw [hid]; ring_nf
        _ ≤ |a-(q+p)|+|q-π/4|+|p-arctan uu|+|arctan uu-arctan us| := by
            have := abs_add_le (a-(q+p)+(q-π/4)+(p-arctan uu)) (arctan uu-arctan us)
            have := abs_add_le (a-(q+p)+(q-π/4)) (p-arctan uu)
            have := abs_add_le (a-(q+p)) (q-π/4)
            linarith
        _ ≤ (u*(13/10)+η)+(13/10*u+η)+(85*u+1/10^10)+11*u := by
            have : |a-(q+p)| ≤ u*(13/10)+η := hsum.trans (by nlinarith)
            linarith
        _ ≤ 100*u := by rw [hu,hη]; norm_num
  -- The octant steps.
  have hτarc : 0 ≤ arctan τ ∧ arctan τ ≤ π/4 := by
    constructor
    · rw [← arctan_zero]; exact arctan_strictMono.monotone hτ0
    · rw [← arctan_one]; exact arctan_strictMono.monotone hτ1
  have hpi := pi_close
  have hpi4 := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  set A1 := if |x| < |y| then π/2-arctan τ else arctan τ
  have hA1 : |a1-A1| ≤ 110*u := by
    rcases h1 with ⟨hxy,hp,hph,ha1⟩ | ⟨hxy,rfl⟩
    · simp only [A1,hxy,↓reduceIte]
      unfold Rnd at hph ha1
      have hph' : |hp-π/2| ≤ 3*u+η := by
        have : |hp-π/2| ≤ |hp-1/2*PIf|+|1/2*PIf-π/2| := abs_sub_le _ _ _
        have h2 : |1/2*PIf-π/2| ≤ 76/100*u := by rw [abs_le]; constructor <;> nlinarith
        have h3 : |hp-1/2*PIf| ≤ 16/10*u+η :=
          hph.trans (by unfold PIf; rw [abs_of_pos (by norm_num)]; nlinarith)
        linarith
      have hus7 : u ≤ 1/10^7 := by rw [hu]; norm_num
      have hha : |hp-a| ≤ 2 := by
        have e1 := abs_le.mp hph'
        have e2 := abs_le.mp hA
        rw [abs_le]; constructor <;> linarith
      have : |a1-(hp-a)| ≤ 2*u+η := ha1.trans (by nlinarith)
      calc |a1-(π/2-arctan τ)| ≤ |a1-(hp-a)|+|hp-π/2|+|a-arctan τ| := by
            have := abs_sub_le a1 (hp-a) (π/2-arctan τ)
            have : |hp-a-(π/2-arctan τ)| ≤ |hp-π/2|+|a-arctan τ| := by
              rw [show hp-a-(π/2-arctan τ) = (hp-π/2)-(a-arctan τ) by ring]; exact abs_sub _ _
            linarith
        _ ≤ 110*u := by rw [hu,hη] at *; nlinarith
    · simp only [A1,hxy,↓reduceIte]; linarith
  have hA1b : |A1| ≤ 16/10 := by
    simp only [A1]; split_ifs
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  set A2 := if x < 0 then π-A1 else A1
  have hA2 : |a2-A2| ≤ 120*u := by
    rcases h2 with ⟨hx,ha2⟩ | ⟨hx,rfl⟩
    · simp only [A2,hx,↓reduceIte]
      unfold Rnd at ha2
      have : |PIf-a1| ≤ 5 := by
        have := abs_sub_abs_le_abs_sub a1 A1
        have := abs_sub PIf a1
        unfold PIf at *; rw [abs_of_pos (by norm_num : (0:ℝ) < 13176795/4194304)] at *
        rw [hu] at *; nlinarith
      have : |a2-(PIf-a1)| ≤ 5*u+η := ha2.trans (by nlinarith)
      calc |a2-(π-A1)| ≤ |a2-(PIf-a1)|+|PIf-π|+|a1-A1| := by
            have := abs_sub_le a2 (PIf-a1) (π-A1)
            have : |PIf-a1-(π-A1)| ≤ |PIf-π|+|a1-A1| := by
              rw [show PIf-a1-(π-A1) = (PIf-π)-(a1-A1) by ring]; exact abs_sub _ _
            linarith
        _ ≤ 120*u := by
            rw [abs_of_pos hpi.1]
            rw [hu,hη] at *; nlinarith
    · simp only [A2,hx,↓reduceIte]; linarith
  have hexact := octant_arg x y hnz
  rw [← hexact,hr]
  unfold octant
  simp only [← hτ]
  change |(if y < 0 then -a2 else a2)-(if y < 0 then -A2 else A2)| ≤ 128*u
  split_ifs
  · rw [show -a2- -A2 = -(a2-A2) by ring,abs_neg]; linarith
  · linarith

/-! ### Skybox texture coordinates -/

/-- `sample_skybox`'s longitude coordinate `atan2_arith(dir.z, dir.x)/(2.0*PI)+0.5`
is within `25u` of `arg(dir.x + i dir.z)/(2π) + 1/2`. -/
theorem skybox_longitude_error (x z lon q v : ℝ)
    (hlon : |lon-Complex.arg ⟨x,z⟩| ≤ 128*u)
    (hq : DivSpec lon (2*PIf) q) (hv : Rnd (q+1/2) v) :
    |v-(Complex.arg ⟨x,z⟩/(2*π)+1/2)| ≤ 25*u := by
  have hu : u = 1/2^24 := rfl
  have hη : η = 1/2^126 := rfl
  have hpi := pi_close
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have harg := Complex.abs_arg_le_pi ⟨x,z⟩
  have h2p : (2*PIf : ℝ) = 13176795/2097152 := by unfold PIf; norm_num
  have hq := hq ⟨by rw [h2p]; norm_num,by rw [h2p]; norm_num⟩
  unfold Wgsl.Div at hq
  unfold Rnd at hv
  set θ := Complex.arg ⟨x,z⟩
  have hlonb : |lon| ≤ 32/10 := by
    have := abs_sub_abs_le_abs_sub lon θ
    rw [hu] at hlon; linarith
  have hqd : |lon/(2*PIf)| ≤ 51/100 := by
    rw [abs_div,h2p,abs_of_pos (by norm_num : (0:ℝ) < 13176795/2097152),div_le_iff₀ (by norm_num)]
    linarith
  have hP : 0 < PIf := by unfold PIf; norm_num
  have h2pos : (0:ℝ) < 2*PIf := by rw [h2p]; norm_num
  have hden : 0 < 2*π*PIf := mul_pos (mul_pos two_pos Real.pi_pos) hP
  have hscale : |lon/(2*PIf)-θ/(2*π)| ≤ 205/10*u+25/100*u := by
    have e1 : |lon/(2*PIf)-θ/(2*PIf)| ≤ 128*u/(2*PIf) := by
      rw [← sub_div,abs_div,abs_of_pos h2pos]
      exact div_le_div_of_nonneg_right hlon h2pos.le
    have e2 : |θ/(2*PIf)-θ/(2*π)| ≤ π*((PIf-π)/(2*π*PIf)) := by
      have hd : 0 ≤ (PIf-π)/(2*π*PIf) := div_nonneg hpi.1.le hden.le
      rw [show θ/(2*PIf)-θ/(2*π) = -θ*((PIf-π)/(2*π*PIf)) by
        field_simp [hP.ne',Real.pi_ne_zero]; ring,abs_mul,abs_neg,abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right harg hd
    have e3 : 128*u/(2*PIf) ≤ 205/10*u := by
      rw [h2p,div_le_iff₀ (by norm_num)]; nlinarith [u_pos]
    have e4 : π*((PIf-π)/(2*π*PIf)) ≤ 25/100*u := by
      rw [show π*((PIf-π)/(2*π*PIf)) = (PIf-π)/(2*PIf) by field_simp [hP.ne',Real.pi_ne_zero],
        h2p,div_le_iff₀ (by norm_num)]
      linarith [hpi.2]
    have := abs_sub_le (lon/(2*PIf)) (θ/(2*PIf)) (θ/(2*π))
    linarith
  have hqv : |q| ≤ 52/100 := by
    have := abs_sub_abs_le_abs_sub q (lon/(2*PIf))
    rw [hu,hη] at hq; nlinarith
  have hv' : |v-(q+1/2)| ≤ 102/100*u+η := hv.trans (by
    have := abs_add_le q (1/2); norm_num at this; nlinarith [u_pos])
  have hq' : |q-lon/(2*PIf)| ≤ 5*u*(51/100)+η := hq.trans (by nlinarith [u_pos])
  have hηu : η ≤ u/2^100 := by rw [hu,hη]; norm_num
  calc |v-(θ/(2*π)+1/2)| ≤ |v-(q+1/2)|+|q-lon/(2*PIf)|+|lon/(2*PIf)-θ/(2*π)| := by
        have := abs_sub_le v (q+1/2) (θ/(2*π)+1/2)
        have := abs_sub_le q (lon/(2*PIf)) (θ/(2*π))
        rw [show q+1/2-(θ/(2*π)+1/2) = q-θ/(2*π) by ring] at *
        linarith
    _ ≤ 25*u := by nlinarith [u_pos]

lemma arg_upper (y σ : ℝ) (hσ : 0 < σ) : Complex.arg ⟨y,σ⟩ = π/2-arctan (y/σ) := by
  have hne : (⟨y,σ⟩ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [Complex.arg_of_im_nonneg_of_ne_zero hσ.le hne,Real.arccos_eq_pi_div_two_sub_arcsin,norm_mk,
    show y^2+σ^2 = σ^2+y^2 by ring]
  change π/2-arcsin (y/√(σ^2+y^2)) = _
  rw [arcsin_div_norm hσ]

/-- Relative error `ε ≤ 1/2` in the vertical coordinate moves the polar angle by
at most `ε`, uniformly up to the poles. -/
lemma arg_vertical (y s s' ε : ℝ) (hs : 0 < s) (hs' : 0 < s') (hε : |s'-s| ≤ ε*s)
    (hε1 : ε ≤ 1/2) : |Complex.arg ⟨y,s'⟩-Complex.arg ⟨y,s⟩| ≤ ε := by
  rw [arg_upper y s' hs',arg_upper y s hs]
  have hε0 : 0 ≤ ε := by
    have := abs_nonneg (s'-s); nlinarith
  set a := y/s; set b := y/s'
  have hab : 0 ≤ a*b := by
    simp only [a,b]; rw [div_mul_div_comm]; exact div_nonneg (mul_self_nonneg y) (by positivity)
  have hid : arctan a-arctan b = arctan ((a-b)/(1+a*b)) := by
    rw [sub_eq_add_neg,← arctan_neg,arctan_add (by nlinarith)]
    congr 1; ring
  rw [show π/2-arctan b-(π/2-arctan a) = arctan a-arctan b by ring,hid]
  refine (by simpa using arctan_lip ((a-b)/(1+a*b)) 0 : |arctan ((a-b)/(1+a*b))| ≤ _).trans ?_
  have hlow : s/2 ≤ s' := by have := (abs_le.mp hε).1; nlinarith
  have heq : (a-b)/(1+a*b) = y*(s'-s)/(s*s'+y^2) := by
    simp only [a,b]; field_simp
  rw [heq,abs_div,abs_mul,abs_of_pos (by positivity : 0 < s*s'+y^2),div_le_iff₀ (by positivity)]
  have hsq : |y| *s ≤ s*s'+y^2 := by
    have := sq_nonneg (|y|-s/2)
    have : s*(s/2) ≤ s*s' := mul_le_mul_of_nonneg_left hlow hs.le
    nlinarith [sq_abs y]
  calc |y| *|s'-s| ≤ |y| *(ε*s) := mul_le_mul_of_nonneg_left hε (abs_nonneg _)
    _ = ε*(|y| *s) := by ring
    _ ≤ ε*(s*s'+y^2) := mul_le_mul_of_nonneg_left hsq hε0

set_option maxHeartbeats 4000000 in
/-- `sample_skybox`'s latitude coordinate `atan2_arith(sqrt(dot(dir.xz,dir.xz)), dir.y)/PI`
is within `52u` of the exact polar angle over `π`, for `2⁻¹⁰⁰ ≤ |dir.xz|² ≤ 2¹⁰⁰`.
WGSL's `sqrt` is `1.0/inverseSqrt`, so `rc` is that division. -/
theorem skybox_latitude_error (x y z px pz r2 i rc lat q : ℝ)
    (hpos : 1/2^100 ≤ x^2+z^2) (hbig : x^2+z^2 ≤ 2^100)
    (hpx : Rnd (x*x) px) (hpz : Rnd (z*z) pz) (hr2 : Rnd (px+pz) r2)
    (hi : InvSqrt r2 i) (hrc : DivSpec 1 i rc)
    (hlat : |lat-Complex.arg ⟨y,rc⟩| ≤ 128*u) (hq : DivSpec lat PIf q) :
    |q-Complex.arg ⟨y,√(x^2+z^2)⟩/π| ≤ 52*u := by
  have hu : u = 1/2^24 := rfl
  have hη : η = 1/2^126 := rfl
  have hu0 := u_pos
  have hη0 := η_pos
  have hηu : η ≤ u/2^100 := by rw [hu,hη]; norm_num
  have hu7 : u ≤ 1/10^7 := by rw [hu]; norm_num
  set R := x^2+z^2 with hR
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hpos
  unfold Rnd at hpx hpz hr2
  have hpx' : |px-x^2| ≤ u*x^2+η := by have := hpx; rwa [abs_mul_self,← pow_two] at this
  have hpz' : |pz-z^2| ≤ u*z^2+η := by have := hpz; rwa [abs_mul_self,← pow_two] at this
  have hx2 := sq_nonneg x
  have hz2 := sq_nonneg z
  have hsum : |px+pz| ≤ (1+u)*R+2*η := by
    have e1 := abs_le.mp hpx'
    have e2 := abs_le.mp hpz'
    rw [abs_le]; constructor <;> nlinarith
  have hηR : η ≤ u*R/4 := by
    have : η*4 ≤ u*R := by
      have := mul_le_mul_of_nonneg_left hpos hu0.le
      rw [hu,hη] at *; nlinarith
    linarith
  have hr2R : |r2-R| ≤ 3*u*R+4*η := by
    have h1 : |r2-(px+pz)| ≤ u*((1+u)*R+2*η)+η := hr2.trans (by nlinarith)
    have h2 : |px+pz-R| ≤ u*R+2*η := by
      have e1 := abs_le.mp hpx'
      have e2 := abs_le.mp hpz'
      rw [abs_le]; constructor <;> nlinarith
    have h3 := abs_sub_le r2 (px+pz) R
    have h4 : u*((1+u)*R+2*η) ≤ u*R+u*u*R+2*η := by nlinarith
    have h5 : u*u*R ≤ u*R/10^6 := by
      have := mul_le_mul_of_nonneg_right hu7 (mul_nonneg hu0.le hR0.le); nlinarith
    linarith
  have hr2R' : |r2-R| ≤ 4*u*R := by linarith
  have hr2lo : R/2 ≤ r2 := by have := (abs_le.mp hr2R').1; nlinarith
  have hr2hi : r2 ≤ 2*R := by have := (abs_le.mp hr2R').2; nlinarith
  have hr20 : 0 < r2 := by linarith
  -- inverseSqrt and the inherited division stay in range
  have hs := Real.sqrt_pos.mpr hr20
  have hslo : 1/2^51 ≤ Real.sqrt r2 := by
    rw [show (1:ℝ)/2^51 = Real.sqrt ((1/2^51)^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hshi : Real.sqrt r2 ≤ 2^51 := by
    rw [show (2:ℝ)^51 = Real.sqrt ((2^51)^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  unfold InvSqrt at hi
  have hi' := abs_le.mp hi
  have hinv : 0 < 1/Real.sqrt r2 := by positivity
  have hinvlo : 1/2^51 ≤ 1/Real.sqrt r2 := one_div_le_one_div_of_le hs hshi
  have hinvhi : 1/Real.sqrt r2 ≤ 2^51 := by
    rw [div_le_iff₀ hs]; nlinarith
  have hipos : 0 < i := by nlinarith
  have hrc := hrc ⟨by rw [abs_of_pos hipos]; nlinarith,by rw [abs_of_pos hipos]; nlinarith⟩
  have hsq := sqrt_inherited r2 i rc hr20 hi hrc
  -- the computed norm against the exact one
  have hsR : |Real.sqrt r2-Real.sqrt R| ≤ 4*u*Real.sqrt R := by
    have hRs := Real.sqrt_pos.mpr hR0
    refine (sqrt_sub_le r2 R hR0).trans ?_
    rw [div_le_iff₀ hRs,mul_assoc,Real.mul_self_sqrt hR0.le]
    linarith
  have hRs := Real.sqrt_pos.mpr hR0
  have hRslo : 1/2^50 ≤ Real.sqrt R := by
    rw [show (1:ℝ)/2^50 = Real.sqrt ((1/2^50)^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hηs : η ≤ u*Real.sqrt R/2^40 := by
    have : η*2^40 ≤ u*Real.sqrt R := by rw [hu,hη]; nlinarith
    linarith
  have hrcR : |rc-Real.sqrt R| ≤ 15*u*Real.sqrt R := by
    have h1 : Real.sqrt r2 ≤ (1+4*u)*Real.sqrt R := by
      have := (abs_le.mp hsR).2; nlinarith
    have h2 : 10*u*Real.sqrt r2 ≤ 10*u*((1+4*u)*Real.sqrt R) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : u*u*Real.sqrt R ≤ u*Real.sqrt R/10^6 := by
      have := mul_le_mul_of_nonneg_right hu7 (mul_nonneg hu0.le hRs.le); nlinarith
    have := abs_sub_le rc (Real.sqrt r2) (Real.sqrt R)
    nlinarith
  have hrc0 : 0 < rc := by
    have := (abs_le.mp hrcR).1
    have : 15*u*Real.sqrt R ≤ Real.sqrt R/2 := by nlinarith
    linarith
  have hvert := arg_vertical y (Real.sqrt R) rc (15*u) hRs hrc0 hrcR (by nlinarith)
  set θ := Complex.arg ⟨y,Real.sqrt R⟩
  have hθ0 : 0 ≤ θ := Complex.arg_nonneg_iff.mpr hRs.le
  have hθπ : θ ≤ π := Complex.arg_le_pi _
  have hlatθ : |lat-θ| ≤ 143*u := by
    have := abs_sub_le lat (Complex.arg ⟨y,rc⟩) θ
    linarith
  have hpi := pi_close
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hP : 0 < PIf := by unfold PIf; norm_num
  have hPv : PIf = 13176795/4194304 := rfl
  have hq := hq ⟨by rw [abs_of_pos hP,hPv]; norm_num,by rw [abs_of_pos hP,hPv]; norm_num⟩
  unfold Wgsl.Div at hq
  have hlatb : |lat/PIf| ≤ 101/100 := by
    rw [abs_div,abs_of_pos hP,div_le_iff₀ hP]
    have := abs_sub_abs_le_abs_sub lat θ
    rw [abs_of_nonneg hθ0] at this
    linarith
  have hq' : |q-lat/PIf| ≤ 51/10*u+η := hq.trans (by nlinarith)
  have hscale : |lat/PIf-θ/π| ≤ 456/10*u+5/10*u := by
    have e1 : |lat/PIf-θ/PIf| ≤ 143*u/PIf := by
      rw [← sub_div,abs_div,abs_of_pos hP]; exact div_le_div_of_nonneg_right hlatθ hP.le
    have hd : 0 ≤ (PIf-π)/(π*PIf) := div_nonneg hpi.1.le (mul_pos Real.pi_pos hP).le
    have e2 : |θ/PIf-θ/π| ≤ π*((PIf-π)/(π*PIf)) := by
      rw [show θ/PIf-θ/π = -θ*((PIf-π)/(π*PIf)) by field_simp [hP.ne',Real.pi_ne_zero]; ring,
        abs_mul,abs_neg,abs_of_nonneg hθ0,abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hθπ hd
    have e3 : 143*u/PIf ≤ 456/10*u := by rw [hPv,div_le_iff₀ (by norm_num)]; nlinarith
    have e4 : π*((PIf-π)/(π*PIf)) ≤ 5/10*u := by
      rw [show π*((PIf-π)/(π*PIf)) = (PIf-π)/PIf by field_simp [hP.ne',Real.pi_ne_zero],
        hPv,div_le_iff₀ (by norm_num)]
      linarith [hpi.2]
    have := abs_sub_le (lat/PIf) (θ/PIf) (θ/π)
    linarith
  have := abs_sub_le q (lat/PIf) (θ/π)
  linarith

end BlackHole.WgslAtan2
