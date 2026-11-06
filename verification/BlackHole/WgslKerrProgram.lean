module

public import BlackHole.WgslLets

/-! `kerr_radius` as a `let`-slot program (obligations F2, F3).

```
fn kerr_radius(x: vec3<f32>, a: vec3<f32>) -> f32 {
    let q = dot(x,x) - dot(a,a);
    let ax = dot(a,x);
    let root = sqrt(q*q + 4.0*ax*ax);
    var r2 = 0.5 * (q + root);
    if q < 0.0 { r2 = 2.0*ax*ax / max(root-q, 1.0e-20); }
    return sqrt(max(r2, 1.0e-12));
}
```

`kerrLets` and `kerrOut` (inputs `x` 0–2, `a` 3–5) are compared with the naga
IR by `tests/translation.rs`. `kerr_slots_error` derives every hypothesis of
the hand-written `WgslKerrRadius.kerr_radius_error` from `SlotsComputes`, in
which each `let` value is computed once, and so gives its `160u` relative
bound for the validated program. The aggregate errors of `q` and `ax` follow
from `dot3_error`; the products by `4.0`, `2.0` and `0.5` are exact up to `η`
(`GExpr.scale`). -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslKerrProgram
open Wgsl WgslExpr GExpr WgslLets

def f32_1em20 : ℚ := 1547425/154742504910672534362390528
def f32_1em12 : ℚ := 2305843/2305843009213693952

def dot3 (p q : Fin 3 → GExpr) : GExpr :=
  add (add (mul (p 0) (q 0)) (mul (p 1) (q 1))) (mul (p 2) (q 2))
def xs (i : Fin 3) : GExpr := input i
def as (i : Fin 3) : GExpr := input (3+i)

/-- Slots: `q` 0, `ax` 1, `root` 2, `r2` 3. -/
def kerrLets : List GExpr :=
  [sub (dot3 xs xs) (dot3 as as),
    dot3 as xs,
    sqrt (add (mul (ref 0) (ref 0)) (mul (scale 2 (ref 1)) (ref 1))),
    lt (ref 0) 0 (div (mul (scale 1 (ref 1)) (ref 1)) (max (sub (ref 2) (ref 0)) (const f32_1em20)))
      (scale (-1) (add (ref 0) (ref 2)))]

def kerrOut : GExpr := sqrt (max (ref 3) (const f32_1em12))

/-- A three-term dot product with correctly rounded operations. -/
theorem dot3_error (t0 t1 t2 m0 m1 m2 s1 d : ℝ) (h0 : Rnd t0 m0) (h1 : Rnd t1 m1)
    (h2 : Rnd t2 m2) (hs : Rnd (m0+m1) s1) (hd : Rnd (s1+m2) d) :
    |d-(t0+t1+t2)| ≤ ((1+u)^3-1)*(|t0|+|t1|+|t2|)+5*(1+u)^3*η := by
  unfold Rnd at *
  have hu := u_pos
  have hη := η_pos
  have g0 : |m0| ≤ (1+u)*|t0|+η := by
    have := abs_sub_abs_le_abs_sub m0 t0; linarith
  have g1 : |m1| ≤ (1+u)*|t1|+η := by
    have := abs_sub_abs_le_abs_sub m1 t1; linarith
  have g2 : |m2| ≤ (1+u)*|t2|+η := by
    have := abs_sub_abs_le_abs_sub m2 t2; linarith
  have hm01 : |m0+m1| ≤ (1+u)*(|t0|+|t1|)+2*η := by
    have := abs_add_le m0 m1; linarith
  have hs1 : |s1-(t0+t1)| ≤ (2*u+u^2)*(|t0|+|t1|)+(3+2*u)*η := by
    have e : |s1-(t0+t1)| ≤ |s1-(m0+m1)|+|m0-t0|+|m1-t1| := by
      have := abs_sub_le s1 (m0+m1) (t0+t1)
      have := abs_add_le (m0-t0) (m1-t1)
      rw [show m0+m1-(t0+t1) = (m0-t0)+(m1-t1) by ring] at *
      linarith
    have := mul_le_mul_of_nonneg_left hm01 hu.le
    nlinarith
  have hsm : |s1+m2| ≤ (1+u)^2*(|t0|+|t1|+|t2|)+(4+2*u)*η := by
    have e1 : |s1+m2| ≤ |t0+t1|+|s1-(t0+t1)|+|m2| := by
      have := abs_add_le (t0+t1) (s1-(t0+t1)); have := abs_add_le s1 m2
      rw [show t0+t1+(s1-(t0+t1)) = s1 by ring] at *; linarith
    have := abs_add_le t0 t1
    have ht2 : (1+u)*|t2| ≤ (1+u)^2*|t2| := by
      have := abs_nonneg t2; nlinarith
    nlinarith
  have e : |d-(t0+t1+t2)| ≤ |d-(s1+m2)|+|s1-(t0+t1)|+|m2-t2| := by
    have := abs_sub_le d (s1+m2) (t0+t1+t2)
    have := abs_add_le (s1-(t0+t1)) (m2-t2)
    rw [show s1+m2-(t0+t1+t2) = (s1-(t0+t1))+(m2-t2) by ring] at *
    linarith
  have := mul_le_mul_of_nonneg_left hsm hu.le
  have ht : 0 ≤ |t0|+|t1| := by positivity
  have ht2 := abs_nonneg t2
  nlinarith [mul_nonneg (mul_nonneg hu.le hu.le) ht, mul_nonneg (mul_nonneg hu.le hu.le) ht2,
    mul_nonneg hu.le ht2, mul_nonneg hu.le hη.le, mul_nonneg (mul_nonneg hu.le hu.le) hη.le]

/-- `dot(x,x) - dot(a,a)` from two dot products with `dot3_error` bounds. -/
theorem sub_error (X A dx da q : ℝ) (hX : 0 ≤ X) (hA : 0 ≤ A)
    (ex : |dx-X| ≤ ((1+u)^3-1)*X+5*(1+u)^3*η) (ea : |da-A| ≤ ((1+u)^3-1)*A+5*(1+u)^3*η)
    (hq : Rnd (dx-da) q) :
    |q-(X-A)| ≤ ((1+u)^6-1)*(X+A)+11*(1+u)^6*η := by
  unfold Rnd at hq
  have hu := u_pos
  have hη := η_pos
  have sub_le (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    have := abs_add_le a (-b); rwa [abs_neg,← sub_eq_add_neg] at this
  have hXA : 0 ≤ X+A := by linarith
  have hd : |dx-da| ≤ X+A+(|dx-X|+|da-A|) := by
    rw [show dx-da = (dx-X)-(da-A)+(X-A) by ring]
    have h1 := abs_add_le ((dx-X)-(da-A)) (X-A)
    have h2 := sub_le (dx-X) (da-A)
    have h3 : |X-A| ≤ X+A := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
    linarith
  have e : |q-(X-A)| ≤ |q-(dx-da)|+(|dx-X|+|da-A|) := by
    rw [show q-(X-A) = (q-(dx-da))+((dx-X)-(da-A)) by ring]
    have := abs_add_le (q-(dx-da)) ((dx-X)-(da-A))
    have := sub_le (dx-X) (da-A)
    linarith
  set E := |dx-X|+|da-A|
  have hE : E ≤ ((1+u)^3-1)*(X+A)+10*(1+u)^3*η := by simp only [E]; linarith
  have s1 : |q-(X-A)| ≤ u*(X+A)+(1+u)*E+η := by
    have := mul_le_mul_of_nonneg_left hd hu.le
    linarith
  have s2 : (1+u)*E ≤ (1+u)*(((1+u)^3-1)*(X+A)+10*(1+u)^3*η) :=
    mul_le_mul_of_nonneg_left hE (by linarith)
  have s3 : u*(X+A)+(1+u)*(((1+u)^3-1)*(X+A)+10*(1+u)^3*η)+η =
      ((1+u)^4-1)*(X+A)+(10*(1+u)^4+1)*η := by ring
  have h4 : (1+u)^4 ≤ (1+u)^6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h6 : 1 ≤ (1+u)^6 := one_le_pow₀ (by linarith)
  have s4 : ((1+u)^4-1)*(X+A) ≤ ((1+u)^6-1)*(X+A) := mul_le_mul_of_nonneg_right (by linarith) hXA
  have s5 : (10*(1+u)^4+1)*η ≤ 11*(1+u)^6*η := mul_le_mul_of_nonneg_right (by linarith) hη.le
  linarith

/-- A product by an exact `c ∈ {2, 4}` then a rounded product. -/
theorem scale_rnd2 (c p m f : ℝ) (hc1 : 1 ≤ c) (hm : |m-c*p| ≤ η) (hf : Rnd (m*p) f) :
    Rnd2 (c*p*p) f := by
  unfold Rnd Rnd2 at *
  have hu := u_pos
  have hη := η_pos
  have hηu : η ≤ u := by norm_num [u, η]
  have hp := abs_nonneg p
  have hmp : |m*p| ≤ c*p^2+η*|p| := by
    rw [abs_mul]
    have : |m| ≤ c*|p|+η := by
      have := abs_sub_abs_le_abs_sub m (c*p)
      rw [abs_mul,abs_of_pos (by linarith : (0:ℝ) < c)] at this; linarith
    have := mul_le_mul_of_nonneg_right this hp
    nlinarith [sq_abs p]
  have e : |f-c*p*p| ≤ |f-m*p|+|p| * η := by
    have := abs_sub_le f (m*p) (c*p*p)
    rw [show m*p-c*p*p = (m-c*p)*p by ring,abs_mul] at this
    nlinarith
  have hcp : |c*p*p| = c*p^2 := by
    rw [show c*p*p = c*p^2 by ring,abs_mul,abs_of_pos (by linarith : (0:ℝ) < c),
      abs_of_nonneg (sq_nonneg p)]
  rw [hcp]
  have hcp0 : 0 ≤ c*p^2 := by positivity
  have hu1 : u ≤ 1 := by norm_num [u]
  have base : |f-c*p*p| ≤ u*(c*p^2)+(1+u)*(η*|p|)+η := by
    have := mul_le_mul_of_nonneg_left hmp hu.le
    nlinarith
  have hηp : (1+u)*(η*|p|) ≤ (u+u^2)*(c*p^2)+2*η := by
    rcases le_total |p| 1 with h | h
    · have : η*|p| ≤ η := by nlinarith
      nlinarith [mul_nonneg (add_nonneg hu.le (sq_nonneg u)) hcp0]
    · have h2 : |p| ≤ p^2 := by nlinarith [sq_abs p]
      have h3 : η*|p| ≤ u*(c*p^2) := by
        have : η*|p| ≤ η*p^2 := mul_le_mul_of_nonneg_left h2 hη.le
        have : η*p^2 ≤ u*(c*p^2) := by
          have := mul_le_mul_of_nonneg_right hηu (sq_nonneg p)
          nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hu.le (sq_nonneg p))]
        linarith
      have := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 1+u)
      nlinarith
  have : (2*u+u^2)*(c*p^2) = u*(c*p^2)+(u+u^2)*(c*p^2) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- Every computation of the validated `kerr_radius` in which each `let`
value is computed once is within `160u` of the exact Kerr radius `√T`, under
the range conditions of `kerr_radius_error`. -/
theorem kerr_slots_error (x0 x1 x2 a0 a1 a2 T : ℝ)
    (hT : T = ((x0*x0+x1*x1+x2*x2-(a0*a0+a1*a1+a2*a2))+
      Real.sqrt ((x0*x0+x1*x1+x2*x2-(a0*a0+a1*a1+a2*a2))^2+4*(a0*x0+a1*x1+a2*x2)^2))/2)
    (haT : a0*a0+a1*a1+a2*a2 ≤ T) (hTmin : 1/2^36 ≤ T) (hTmax : T ≤ 2^120) (vals : List ℝ)
    (hs : SlotsComputes (fun i => [x0,x1,x2,a0,a1,a2].getD i 0) kerrLets [] vals) (r : ℝ)
    (hr : Computes (env (fun i => [x0,x1,x2,a0,a1,a2].getD i 0) vals) kerrOut r) :
    |r-Real.sqrt T| ≤ 160*u*Real.sqrt T := by
  obtain ⟨q,hq,p,hp,root,hroot,r2,hr2,rfl⟩ := hs
  simp only [List.nil_append,List.cons_append] at *
  simp only [kerrOut,dot3,xs,as,ref,env,letBase,Computes] at hq hp hroot hr2 hr
  norm_num at hq hp hroot hr2 hr
  obtain ⟨dx,⟨s1x,⟨mx0,hmx0,mx1,hmx1,hsx⟩,mx2,hmx2,hdx⟩,da,⟨s1a,⟨ma0,hma0,ma1,hma1,hsa⟩,ma2,hma2,hda⟩,
    hqr⟩ := hq
  obtain ⟨s1p,⟨mp0,hmp0,mp1,hmp1,hsp⟩,mp2,hmp2,hpd⟩ := hp
  obtain ⟨sv,⟨qq,hqq,fp,⟨m4,hm4,hfp⟩,hsv⟩,hrt⟩ := hroot
  have ex := dot3_error _ _ _ _ _ _ _ _ hmx0 hmx1 hmx2 hsx hdx
  have ea := dot3_error _ _ _ _ _ _ _ _ hma0 hma1 hma2 hsa hda
  have ep := dot3_error _ _ _ _ _ _ _ _ hmp0 hmp1 hmp2 hsp hpd
  simp only [abs_mul_self] at ex ea
  have hX : 0 ≤ x0*x0+x1*x1+x2*x2 := by nlinarith [mul_self_nonneg x0,mul_self_nonneg x1,mul_self_nonneg x2]
  have hA : 0 ≤ a0*a0+a1*a1+a2*a2 := by nlinarith [mul_self_nonneg a0,mul_self_nonneg a1,mul_self_nonneg a2]
  have hqE := sub_error _ _ _ _ _ hX hA ex ea hqr
  have amgm (a x : ℝ) : |a*x| ≤ (a*a+x*x)/2 := by
    rw [abs_mul]
    have := two_mul_le_add_sq |a| |x|
    rw [sq_abs,sq_abs] at this
    nlinarith
  have h20 : ((f32_1em20 : ℚ) : ℝ) = 1547425/154742504910672534362390528 := by norm_num [f32_1em20]
  have h12 : ((f32_1em12 : ℚ) : ℝ) = 2305843/2305843009213693952 := by norm_num [f32_1em12]
  rw [h12] at hr
  refine kerr_radius_error (x0*x0+x1*x1+x2*x2) (a0*a0+a1*a1+a2*a2) (a0*x0+a1*x1+a2*x2)
    (|a0*x0|+|a1*x1|+|a2*x2|) T hX hA ?_ ?_ ?_ hT haT hTmin hTmax
    q p qq fp sv root hqE ep hqq (scale_rnd2 4 p m4 fp (by norm_num) hm4 hfp) hsv hrt r2 r ?_ hr
  · have : (x0*x0+x1*x1+x2*x2)*(a0*a0+a1*a1+a2*a2)-(a0*x0+a1*x1+a2*x2)^2 =
        (a0*x1-a1*x0)^2+(a0*x2-a2*x0)^2+(a1*x2-a2*x1)^2 := by ring
    have := sq_nonneg (a0*x1-a1*x0)
    have := sq_nonneg (a0*x2-a2*x0)
    have := sq_nonneg (a1*x2-a2*x1)
    linarith
  · have := abs_add_le (a0*x0+a1*x1) (a2*x2)
    have := abs_add_le (a0*x0) (a1*x1)
    linarith
  · linarith [amgm a0 x0,amgm a1 x1,amgm a2 x2]
  · rcases hr2 with ⟨hneg,num,⟨m2,hm2,hnum⟩,den,hden,hdiv⟩ | ⟨hpos,sA,hsA,hhalf⟩
    · rw [h20] at hdiv
      exact Or.inr ⟨hneg,num,den,scale_rnd2 2 p m2 num (by norm_num) hm2 hnum,hden,hdiv⟩
    · refine Or.inl ⟨hpos,sA,hsA,?_⟩
      unfold Rnd
      rw [show sA/2 = 1/2*sA by ring]
      linarith [mul_nonneg u_pos.le (abs_nonneg (1/2*sA))]

end BlackHole.WgslKerrProgram
