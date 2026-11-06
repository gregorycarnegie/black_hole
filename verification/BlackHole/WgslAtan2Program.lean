module

public import BlackHole.WgslAtan2
public import BlackHole.WgslLets

/-! `atan2_arith` as a `let`-slot program (obligations F2, F3).

```
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

`atan2Lets` and `atan2Out` (inputs `y` 0, `x` 1) are compared with the naga
IR by `tests/translation.rs`. `atan2_slots_error` derives the execution trace
of `WgslAtan2.atan2_arith_error` from `SlotsComputes`, in which each `let`
value is computed once, as the naga IR computes it, and so gives the `128u`
bound for the validated program. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslAtan2Program
open Wgsl WgslPoly WgslExpr GExpr WgslLets WgslAtan2

/-- A one-input polynomial program as a `GExpr` reading `u`. -/
def ofP (u : GExpr) : PExpr → GExpr
  | .input _ => u
  | .const c => const c
  | .add a b => add (ofP u a) (ofP u b)
  | .sub a b => sub (ofP u a) (ofP u b)
  | .mul a b => mul (ofP u a) (ofP u b)
  | .neg a => neg (ofP u a)
  | .divc a c => div (ofP u a) (const c)

/-- `f32(π)` and `f32(tan(π/8))` as exact constants. -/
def PIq : ℚ := 13176795/4194304
def TANq : ℚ := 13898701/33554432

/-- Slots: `ax` 0, `ay` 1, `hi` 2, `t` 3, `atan_poly(t)` 4, the reduced
argument 5, its polynomial 6, then `a` after each of the four `if`s, 7–10. -/
def atan2Lets : List GExpr :=
  [abs (input 1), abs (input 0), max (ref 0) (ref 1), div (min (ref 0) (ref 1)) (ref 2),
    ofP (ref 3) polyE,
    div (sub (ref 3) (const 1)) (add (ref 3) (const 1)),
    ofP (ref 5) polyE,
    lt2 (const TANq) (ref 3) (add (const (PIq/4)) (ref 6)) (ref 4),
    lt2 (ref 0) (ref 1) (sub (const (PIq/2)) (ref 7)) (ref 7),
    lt (input 1) 0 (sub (const PIq) (ref 8)) (ref 8),
    lt (input 0) 0 (neg (ref 9)) (ref 9)]

/-- The early return for `hi == 0`. -/
def atan2Out : GExpr := lt (neg (ref 2)) 0 (ref 10) (const 0)

theorem ofP_computes (w : ℕ → ℝ) (u : GExpr) (t : ℝ) (hu : ∀ z, Computes w u z → z = t) :
    ∀ (e : PExpr) (y : ℝ), Computes w (ofP u e) y → e.Computes (fun _ => t) y
  | .input _, y, h => hu y h
  | .const c, y, h => h
  | .add a b, y, ⟨ya,yb,ha,hb,h⟩ =>
    ⟨ya,yb,ofP_computes w u t hu a ya ha,ofP_computes w u t hu b yb hb,h⟩
  | .sub a b, y, ⟨ya,yb,ha,hb,h⟩ =>
    ⟨ya,yb,ofP_computes w u t hu a ya ha,ofP_computes w u t hu b yb hb,h⟩
  | .mul a b, y, ⟨ya,yb,ha,hb,h⟩ =>
    ⟨ya,yb,ofP_computes w u t hu a ya ha,ofP_computes w u t hu b yb hb,h⟩
  | .neg a, y, ⟨ya,ha,h⟩ => ⟨ya,ofP_computes w u t hu a ya ha,h⟩
  | .divc a c, y, ⟨ya,yb,ha,hb,h⟩ => by
    refine ⟨ya,ofP_computes w u t hu a ya ha,?_⟩
    have : yb = (c : ℝ) := hb
    rwa [this] at h

lemma rnd_exact (x : ℝ) : Rnd x x := by
  unfold Rnd; have := η_pos; have := u_pos; simp; positivity

lemma PIq_eq : ((PIq : ℚ) : ℝ) = PIf := by norm_num [PIq,PIf]
lemma TANq_eq : ((TANq : ℚ) : ℝ) = TANf := by norm_num [TANq,TANf]

/-- Every computation of the validated program in which each `let` value is
computed once is within `128u` of `atan2(y, x)`. -/
theorem atan2_slots_error (x y : ℝ) (hnz : x ≠ 0 ∨ y ≠ 0)
    (hlo : 1/2^126 ≤ max |x| |y|) (hhi : max |x| |y| ≤ 2^126) (vals : List ℝ)
    (hs : SlotsComputes (fun i => if i = 0 then y else x) atan2Lets [] vals) (r : ℝ)
    (hr : Computes (env (fun i => if i = 0 then y else x) vals) atan2Out r) :
    |r-Complex.arg ⟨x,y⟩| ≤ 128*u := by
  obtain ⟨y0,h0,y1,h1,y2,h2,y3,h3,y4,h4,y5,h5,y6,h6,y7,h7,y8,h8,y9,h9,y10,h10,rfl⟩ := hs
  simp only [List.nil_append,List.cons_append] at *
  simp only [atan2Out,ref,env,letBase,Computes] at h0 h1 h2 h3 h5 h7 h8 h9 h10 hr
  norm_num at h0 h1 h2 h3 h5 h7 h8 h9 h10 hr
  have hu (k : ℕ) (vs : List ℝ) (hk : k < vs.length) (z : ℝ)
      (hz : Computes (env (fun i => if i = 0 then y else x) vs) (ref k) z) : z = vs[k] := by
    simp only [ref,env,Computes] at hz
    subst hz
    simp [hk,letBase]
  have p4 := ofP_computes _ _ _ (hu 3 [y0,y1,y2,y3] (by simp)) polyE y4 h4
  have p6 := ofP_computes _ _ _ (hu 5 [y0,y1,y2,y3,y4,y5] (by simp)) polyE y6 h6
  simp only [List.getElem_cons_succ,List.getElem_cons_zero] at p4 p6
  subst h0 h1 h2
  rw [PIq_eq] at h7 h8 h9
  rw [TANq_eq] at h7
  obtain ⟨dm,hdm,dp,hdp,hdiv⟩ := h5
  refine atan2_arith_error x y hnz hlo hhi y3 h3 y7 ?_ y8 ?_ y9 ?_ r ?_
  · rcases h7 with ⟨hlt,hq⟩ | ⟨hle,rfl⟩
    · refine Or.inr ⟨hlt,dm,dp,y5,y6,PIf/4,hdm,hdp,hdiv,p6,?_,hq⟩
      rw [show 1/4*PIf = PIf/4 by ring]; exact rnd_exact _
    · exact Or.inl ⟨not_lt.mpr hle,p4⟩
  · rcases h8 with ⟨hlt,hq⟩ | ⟨hle,rfl⟩
    · refine Or.inl ⟨hlt,PIf/2,?_,hq⟩
      rw [show 1/2*PIf = PIf/2 by ring]; exact rnd_exact _
    · exact Or.inr ⟨not_lt.mpr hle,rfl⟩
  · rcases h9 with h | ⟨hle,rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.mpr hle,rfl⟩
  · rcases hr with ⟨_,rfl⟩ | ⟨hle,_⟩
    · rcases h10 with ⟨hy,rfl⟩ | ⟨hy,rfl⟩
      · simp [hy]
      · simp [not_lt.mpr hy]
    · linarith

end BlackHole.WgslAtan2Program
