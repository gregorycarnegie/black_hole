module

public import BlackHole.WgslKerrProgram

/-! The arithmetic `sincos` as a `let`-slot program (obligations F2, F3).

```
fn sincos(x: f32) -> vec2<f32> {
    let k = round(x*TWO_OVER_PI);
    let r = clamp((x-k*PIO2_HI)-k*PIO2_LO,-1.0,1.0);
    let r2 = r*r;
    let s = r*(1.0+r2*(-1.0/6.0+ ... +r2*(1.0/6227020800.0)));
    let c = 1.0+r2*(-0.5+ ... +r2*(-1.0/87178291200.0));
    let q = i32(k) & 3;
    if q == 0 { return vec2<f32>(s,c); }
    if q == 1 { return vec2<f32>(c,-s); }
    if q == 2 { return vec2<f32>(-s,-c); }
    return vec2<f32>(-c,s);
}
```

`sincosLets` and `sincosOut` (input `x` 0) are compared with the naga IR by
`tests/translation.rs`, which reads `i32(k) & 3` as `k mod 4` only for `k` the
result of `round` (an integer, exact in `i32` for `|x| ≤ 2^18`) and the four
returns as `GExpr.qsel`. The coefficients are the binary32 values naga folds
the shader's quotients to. `sincos_slots_error` derives `SinCosComputes`, the
hand-written model of `WgslSinCos`, from `SlotsComputes`, so the `128u(1+|x|)`
bound of `sincos_spec` holds for the compared program. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslSinCosProgram
open Wgsl WgslExpr GExpr WgslLets

def TWOq : ℚ := 10680707/16777216
def HIq : ℚ := 13176795/8388608
def LOq : ℚ := -6151831/140737488355328

/-- The binary32 coefficients of the two Horner polynomials. -/
def sinCs : List ℚ := [1, -11184811/67108864, 8947849/1073741824, -13634817/68719476736,
  12119837/4398046511104, -14103083/562949953421312, 11571761/72057594037927936]
def cosCs : List ℚ := [1, -1/2, 11184811/268435456, -11930465/8589934592,
  13634817/549755813888, -4847935/17592186044416, 9402055/4503599627370496,
  -13224869/1152921504606846976]

def hornerG (y : GExpr) : List ℚ → GExpr
  | [] => const 0
  | [c] => const c
  | c :: cs => add (const c) (mul y (hornerG y cs))

/-- Slots: `x*TWO_OVER_PI` 0, `k` 1, the reduced argument 2, `r` 3, `r2` 4,
`s` 5, `c` 6. -/
def sincosLets : List GExpr :=
  [mul (input 0) (const TWOq), round (ref 0),
    sub (sub (input 0) (mul (ref 1) (const HIq))) (mul (ref 1) (const LOq)),
    min (max (ref 2) (const (-1))) (const 1),
    mul (ref 3) (ref 3),
    mul (ref 3) (hornerG (ref 4) sinCs),
    hornerG (ref 4) cosCs]

def sincosOut (j : Bool) : GExpr := qsel j (ref 1) (ref 5) (ref 6)

theorem horner_computes (w : ℕ → ℝ) (y : GExpr) (yy : ℝ) (hy : ∀ z, Computes w y z → z = yy) :
    ∀ (c : ℚ) (cs : List ℚ) (h : ℝ), Computes w (hornerG y (c :: cs)) h →
      HornerComp ((c :: cs).map (fun q : ℚ => (q : ℝ))) yy h
  | c, [], h, hc => hc
  | c, c' :: cs, h, ⟨ya,yb,hya,⟨yy',t,hyy,ht,hm⟩,hh⟩ => by
    have hya : ya = c := hya
    have e := hy yy' hyy
    subst hya
    rw [e] at hm
    exact ⟨t,yb,horner_computes w y yy hy c' cs t ht,hm,hh⟩

lemma clamp_eq (r0 : ℝ) : min (max r0 (-1)) 1 = max (-1) (min 1 r0) := by
  simp only [max_def,min_def]
  split_ifs <;> linarith

lemma rnd_neg {x y : ℝ} (h : Rnd x y) : Rnd (-x) (-y) := by
  unfold Rnd at *; rwa [show -y - -x = -(y-x) by ring,abs_neg,abs_neg]

lemma rnd_self (x : ℝ) : Rnd x x := by
  unfold Rnd; have := η_pos; have := u_pos; simp; positivity

/-- Every computation of the validated `sincos` in which each `let` value is
computed once is within `128u(1+|x|)` of `sin x` and `cos x` for `|x| ≤ 2^18`. -/
theorem sincos_slots_error (x : ℝ) (hx : |x| ≤ 2^18) (vals : List ℝ)
    (hs : SlotsComputes (fun _ => x) sincosLets [] vals) (y0 y1 : ℝ)
    (h0 : Computes (env (fun _ => x) vals) (sincosOut false) y0)
    (h1 : Computes (env (fun _ => x) vals) (sincosOut true) y1) :
    |y0-Real.sin x| ≤ 128*u*(1+|x|) ∧ |y1-Real.cos x| ≤ 128*u*(1+|x|) := by
  obtain ⟨t,ht,k,hk,r0,hr0,r,hr,yy,hyy,s,hsc,c,hcc,rfl⟩ := hs
  simp only [List.nil_append,List.cons_append] at *
  have rd (i : ℕ) (vs : List ℝ) (hi : i < vs.length) (z : ℝ)
      (hz : Computes (env (fun _ => x) vs) (ref i) z) : z = vs[i] := by
    simp only [ref,env,Computes] at hz
    subst hz
    simp [hi,letBase]
  simp only [sincosOut,ref,env,letBase,Computes] at ht hk hr0 hr hyy h0 h1
  norm_num at ht hk hr0 hr hyy h0 h1
  obtain ⟨⟨n,rfl⟩,hkt⟩ := hk
  obtain ⟨d1,⟨m1,hm1,hd1⟩,m2,hm2,hr0'⟩ := hr0
  obtain ⟨n0,hn0,rfl⟩ := h0
  obtain ⟨n1,hn1,rfl⟩ := h1
  rw [show n0 = n by exact_mod_cast hn0.symm,show n1 = n by exact_mod_cast hn1.symm]
  obtain ⟨yr,hS,hyr,hHs,hrs⟩ := hsc
  have hyr' := rd 3 [t,(n:ℝ),r0,r,yy] (by simp) yr hyr
  simp only [List.getElem_cons_succ,List.getElem_cons_zero] at hyr'
  subst hyr'
  have r4 (vs : List ℝ) (hv : 4 < vs.length) (z : ℝ) (hz : Computes (env (fun _ => x) vs) (ref 4) z) :
      z = vs[4] := rd 4 vs hv z hz
  have hs' := horner_computes _ (ref 4) yy
    (fun z hz => by simpa using r4 [t,(n:ℝ),r0,yr,yy] (by simp) z hz) 1 _ hS hHs
  have hc' := horner_computes _ (ref 4) yy
    (fun z hz => by simpa using r4 [t,(n:ℝ),r0,yr,yy,s] (by simp) z hz) 1 _ c hcc
  have hspec := sincos_spec (out := quadSel (n % 4) s c) ?_ hx
  · exact ⟨by simpa [qpick] using hspec.1,by simpa [qpick] using hspec.2⟩
  have hd1' : Rnd (x+-m1) d1 := by rwa [← sub_eq_add_neg]
  have hr0'' : Rnd (d1+-m2) r0 := by rwa [← sub_eq_add_neg]
  have hred := WgslKerrProgram.dot3_error _ _ _ _ _ _ _ _ (rnd_self x) (rnd_neg hm1) (rnd_neg hm2)
    hd1' hr0''
  simp only [abs_neg] at hred
  norm_num [TWOq,HIq,LOq] at ht hred
  refine ⟨t,n,r0,yr,yy,sinCs.map (fun q : ℚ => (q : ℝ)),cosCs.map (fun q : ℚ => (q : ℝ)),_,s,c,
    ht,hkt,?_,by rw [hr,clamp_eq],hyy,?_,?_,hs',hrs,hc',rfl⟩
  · rw [show x-n*(13176795/8388608:ℝ)-n*(-6151831/140737488355328) =
      x+-(n*(13176795/8388608))+-(n*(-6151831/140737488355328)) by ring,abs_mul,abs_mul]
    norm_num
    linarith [hred]
  · simp only [sinCoeffs,sinCs,List.map_cons,List.map_nil,List.forall₂_cons,List.Forall₂.nil,
      and_true,Rnd,u,η]
    norm_num
  · simp only [cosCoeffs,cosCs,List.map_cons,List.map_nil,List.forall₂_cons,List.Forall₂.nil,
      and_true,Rnd,u,η]
    norm_num

end BlackHole.WgslSinCosProgram
