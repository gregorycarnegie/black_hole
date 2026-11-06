module

public import BlackHole.WgslLets
public import BlackHole.WgslTransferPhi

/-! The polarized transfer helpers of `geodesic.wesl` as `let`-slot programs
(obligations F2, F3, T2, T3).

```
fn faraday_rotation(rho: vec3<f32>, ds: f32) -> mat3x3<f32>
fn transfer_phi(z: vec2<f32>) -> vec2<f32>
fn absorption_integral(alpha: f32, ds: f32) -> f32
fn polarized_cell(j: vec4<f32>, alpha: f32, rho: vec3<f32>, ds: f32) -> vec4<f32>
```

`tests/translation.rs` compares these programs with the naga IR, with calls
to the arithmetic `sincos` read as `sinS`/`cosS` (`WgslSinCosProgram`). The
`transfer_phi` series loop unrolls into twenty slots, so the expanded tree
is exactly the WGSL evaluation and `WgslExpr`'s running bound applies to all
three programs. `transfer_phi_slots_error` derives the execution traces of
`WgslTransferPhi` from the compared `transfer_phi`, so its closed-form bound,
`1200u` per component of `φ(z)` for `0 ≤ Re z ≤ 2⁶²`, `|Im z| ≤ 2¹⁸`, holds
for it. The constants are the binary32 values of the shader's literals and
quotients. -/

@[expose] public section

namespace BlackHole.WgslTransferProgram
open WgslExpr GExpr WgslLets

/-- binary32 `1/(k+1)!`, `k = 0, …, 10`. -/
def phiCs : List ℚ := [1, 1/2, 11184811/67108864, 11184811/268435456, 8947849/1073741824,
  11930465/8589934592, 13634817/68719476736, 13634817/549755813888,
  12119837/4398046511104, 4847935/17592186044416, 14103083/562949953421312]

/-- binary32 `1.0e-20` and `1.0e-5`. -/
def tinyQ : ℚ := 1547425/154742504910672534362390528
def cutQ : ℚ := 2748779/274877906944

/-- The series accumulator before iteration `i` (`k = 9 - i`), for slots
from `b`: `(c[10], 0)`, then the previous iteration's slots. -/
def accX (b i : ℕ) : GExpr := if i = 0 then const (phiCs.getD 10 0) else ref (b+2*i-1)
def accY (b i : ℕ) : GExpr := if i = 0 then const 0 else ref (b+2*i)

/-- Iteration `i` of the series loop: `acc = c[k] - z*acc`, `k = 9 - i`. -/
def hornerSlot (b : ℕ) (zx zy : GExpr) (i : ℕ) : List GExpr :=
  [sub (const (phiCs.getD (9-i) 0)) (sub (mul zx (accX b i)) (mul zy (accY b i))),
    neg (add (mul zx (accY b i)) (mul zy (accX b i)))]

def hornerSlots (b : ℕ) (zx zy : GExpr) (n : ℕ) : List GExpr :=
  (List.range n).flatMap (hornerSlot b zx zy)

/-- `transfer_phi(z)` from slot `b`: `dot(z,z)` at `b`, iteration `i` at
`b+1+2i` (re) and `b+2+2i` (im), `exp(-z.x)` at `b+21`, and `1 - exp(-z)`
at `b+22` (re) and `b+23` (im). -/
def phiLets (b : ℕ) (zx zy : GExpr) : List GExpr :=
  [add (mul zx zx) (mul zy zy)] ++ hornerSlots b zx zy 10 ++
  [exp (neg zx), sub (const 1) (mul (ref (b+21)) (cosS zy)), mul (ref (b+21)) (sinS zy)]

/-- Component `im` of `transfer_phi(z)` over the slots from `b`. -/
def phiOut (b : ℕ) (zx zy : GExpr) (im : Bool) : GExpr :=
  if im then
    lt (ref b) (1/4) (ref (b+20)) (div (sub (mul (ref (b+23)) zx) (mul (ref (b+22)) zy)) (ref b))
  else
    lt (ref b) (1/4) (ref (b+19)) (div (add (mul (ref (b+22)) zx) (mul (ref (b+23)) zy)) (ref b))

/-! `transfer_phi`: `z` inputs 0–1. -/

def phiProgLets : List GExpr := phiLets 0 (input 0) (input 1)
def phiProgOut (im : Bool) : GExpr := phiOut 0 (input 0) (input 1) im

/-! `faraday_rotation`: `rho` inputs 0–2, `ds` input 3. Slots: `w` 0, `axis`
1–3, `angle` 4, `s` 5, `c` 6. -/

def faradayLets : List GExpr :=
  [sqrt (add (add (mul (input 0) (input 0)) (mul (input 1) (input 1))) (mul (input 2) (input 2))),
    div (input 0) (max (ref 0) (const tinyQ)), div (input 1) (max (ref 0) (const tinyQ)),
    div (input 2) (max (ref 0) (const tinyQ)),
    mul (ref 0) (input 3), sinS (ref 4), cosS (ref 4)]

def axisR (i : Fin 3) : GExpr := ref (1+i)

/-- Entry `[col][row]` of `cross_matrix`. -/
def crossEntry (col row : Fin 3) : GExpr :=
  match col.val, row.val with
  | 0, 1 => axisR 2 | 0, 2 => neg (axisR 1)
  | 1, 0 => neg (axisR 2) | 1, 2 => axisR 0
  | 2, 0 => axisR 1 | 2, 1 => neg (axisR 0)
  | _, _ => const 0

/-- Entry `[col][row]` of `c*identity + s*cross_matrix + (1-c)*aa`. -/
def faradayOut (col row : Fin 3) : GExpr :=
  add (add (mul (ref 6) (const (if col = row then 1 else 0))) (mul (ref 5) (crossEntry col row)))
    (mul (sub (const 1) (ref 6)) (mul (axisR row) (axisR col)))

/-! `polarized_cell`: `j` inputs 0–3, `alpha` 4, `rho` 5–7, `ds` 8. Slots:
`transfer_phi(alpha*ds, 0)` 0–23, `integral` 24, `w` 25, `axis` 26–28,
`dot(axis, j.yzw)` 29, `parallel` 30–32, `perpendicular` 33–35,
`transfer_phi(alpha*ds, -w*ds)` 36–59, `ic` 60, `is` 61,
`cross(axis, perpendicular)` 62–64. -/

def zAbs : GExpr := mul (input 4) (input 8)
def zRot : GExpr := mul (neg (ref 25)) (input 8)

def cellAxis (i : ℕ) : GExpr := ref (26+i)
def cellPerp (i : ℕ) : GExpr := ref (33+i)

def cellLets : List GExpr :=
  phiLets 0 zAbs (const 0) ++
  [mul (input 8) (phiOut 0 zAbs (const 0) false),
    sqrt (add (add (mul (input 5) (input 5)) (mul (input 6) (input 6))) (mul (input 7) (input 7))),
    div (input 5) (ref 25), div (input 6) (ref 25), div (input 7) (ref 25),
    add (add (mul (cellAxis 0) (input 1)) (mul (cellAxis 1) (input 2))) (mul (cellAxis 2) (input 3)),
    mul (cellAxis 0) (ref 29), mul (cellAxis 1) (ref 29), mul (cellAxis 2) (ref 29),
    sub (input 1) (ref 30), sub (input 2) (ref 31), sub (input 3) (ref 32)] ++
  phiLets 36 zAbs zRot ++
  [mul (input 8) (phiOut 36 zAbs zRot false), mul (input 8) (phiOut 36 zAbs zRot true),
    sub (mul (cellAxis 1) (cellPerp 2)) (mul (cellAxis 2) (cellPerp 1)),
    sub (mul (cellAxis 2) (cellPerp 0)) (mul (cellAxis 0) (cellPerp 2)),
    sub (mul (cellAxis 0) (cellPerp 1)) (mul (cellAxis 1) (cellPerp 0))]

/-- Component `k` of the returned Stokes vector. The intensity is the same
on both branches; the others take `j*integral` when `w*ds < 1e-5`. -/
def cellOut (k : Fin 4) : GExpr :=
  if k.val = 0 then mul (input 0) (ref 24) else
  lt (mul (ref 25) (input 8)) cutQ (mul (input k.val) (ref 24))
    (add (add (mul (ref 24) (ref (29+k.val))) (mul (ref 60) (ref (32+k.val))))
      (mul (ref 61) (ref (61+k.val))))

theorem cellLets_length : cellLets.length = 65 := by decide
theorem phiLets_length (b : ℕ) (zx zy : GExpr) : (phiLets b zx zy).length = 24 := by
  simp [phiLets, hornerSlots, hornerSlot, List.range_succ]

/-! ### The validated `transfer_phi` satisfies the hand-written bounds

`transfer_phi_slots_error` derives the execution traces of `WgslTransferPhi`
(`CHornerComp`, `ExpW`, the `sincos` and quotient roundings) from
`SlotsComputes`, so its closed-form bounds hold for the compared program. -/

open Wgsl

/-- `e` has value `v` in every environment extending the slots `vs`. -/
def Det (w : ℕ → ℝ) (vs : List ℝ) (e : GExpr) (v : ℝ) : Prop :=
  ∀ more z, Computes (env w (vs ++ more)) e z → z = v

lemma Det.app {w vs e v z} (h : Det w vs e v) (hz : Computes (env w vs) e z) : z = v :=
  h [] z (by simpa using hz)

lemma Det.mono {w vs e v} (h : Det w vs e v) (more : List ℝ) : Det w (vs ++ more) e v :=
  fun m z hz => h (more ++ m) z (by simpa using hz)

lemma det_input {w vs i} (hi : i < letBase) : Det w vs (input i) (w i) := fun _ z hz => by
  simpa [Computes, env, Nat.not_le.mpr hi] using hz

lemma det_const {w vs} (c : ℚ) : Det w vs (const c) c := fun _ _ hz => hz

lemma getD_app {l m : List ℝ} {k : ℕ} (d d' : ℝ) (hk : k < l.length) :
    (l ++ m).getD k d = l.getD k d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

lemma det_ref {w vs k} (hk : k < vs.length) : Det w vs (ref k) (vs.getD k 0) := fun more z hz => by
  simp only [ref, Computes, env, letBase, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left] at hz
  rw [hz, getD_app _ 0 hk]

lemma slots_append (w : ℕ → ℝ) : ∀ (l1 l2 : List GExpr) (done vals : List ℝ),
    SlotsComputes w (l1 ++ l2) done vals →
      ∃ mid, SlotsComputes w l1 done mid ∧ SlotsComputes w l2 mid vals
  | [], _, _, _, h => ⟨_, rfl, h⟩
  | _ :: l1, l2, _, vals, ⟨y, hy, h⟩ => by
    obtain ⟨mid, h1, h2⟩ := slots_append w l1 l2 _ vals h
    exact ⟨mid, ⟨y, hy, h1⟩, h2⟩

/-- One loop iteration, from the values of `z` and the accumulator. -/
lemma iter_step {w vs zx zy A B X Y a b re im} {c : ℚ} (hX : Det w vs zx X) (hY : Det w vs zy Y)
    (hA : Det w vs A a) (hB : Det w vs B b)
    (hre : Computes (env w vs) (sub (const c) (sub (mul zx A) (mul zy B))) re)
    (him : Computes (env w (vs ++ [re])) (neg (add (mul zx B) (mul zy A))) im) :
    ∃ p q t1 r s t2 : ℝ, Rnd (X*a) p ∧ Rnd (Y*b) q ∧ Rnd (p-q) t1 ∧ Rnd (X*b) r ∧
      Rnd (Y*a) s ∧ Rnd (r+s) t2 ∧ Rnd ((c:ℝ)-t1) re ∧ im = -t2 := by
  obtain ⟨yc, t1, hc, ⟨p, q, ⟨x1, a1, hx1, ha1, hp⟩, ⟨y1, b1, hy1, hb1, hq⟩, ht1⟩, hre⟩ := hre
  obtain ⟨t2, ⟨r, s, ⟨x2, b2, hx2, hb2, hr⟩, ⟨y2, a2, hy2, ha2, hs⟩, ht2⟩, rfl⟩ := him
  have hc : yc = c := hc
  rw [hX.app hx1, hA.app ha1] at hp
  rw [hY.app hy1, hB.app hb1] at hq
  rw [hX _ _ hx2, hB _ _ hb2] at hr
  rw [hY _ _ hy2, hA _ _ ha2] at hs
  rw [hc] at hre
  exact ⟨p, q, t1, r, s, t2, hp, hq, ht1, hr, hs, ht2, hre, rfl⟩

/-- The binary32 series coefficients as reals. -/
def phiB : List ℝ := phiCs.map (fun q : ℚ => (q : ℝ))

/-- The accumulator after `n` iterations. -/
def accC (b n : ℕ) (vs : List ℝ) : ℂ :=
  if n = 0 then ⟨((phiCs.getD 10 0 : ℚ) : ℝ), 0⟩ else ⟨vs.getD (b+2*n-1) 0, vs.getD (b+2*n) 0⟩

lemma phiB_drop (n : ℕ) (hn : n < 10) : ∃ cT' cTs, phiB.drop (10-n) = cT' :: cTs ∧
    phiB.drop (9-n) = ((phiCs.getD (9-n) 0 : ℚ) : ℝ) :: cT' :: cTs := by
  interval_cases n <;> simp [phiB, phiCs]

lemma horner_trace {w : ℕ → ℝ} {b : ℕ} {zx zy : GExpr} {X Y : ℝ} :
    ∀ n ≤ 10, ∀ done mid : List ℝ, done.length = b+1 → Det w done zx X → Det w done zy Y →
      SlotsComputes w (hornerSlots b zx zy n) done mid →
      (∃ L, mid = done ++ L ∧ L.length = 2*n) ∧ Det w mid (accX b n) (accC b n mid).re ∧
        Det w mid (accY b n) (accC b n mid).im ∧
        CHornerComp ⟨X, Y⟩ (phiB.drop (10-n)) (accC b n mid)
  | 0, _, done, mid, _, _, _, hs => by
    have hm : mid = done := hs
    subst hm
    refine ⟨⟨[], by simp, rfl⟩, ?_, ?_, ?_⟩
    · simpa [accX, accC] using det_const (w := w) (vs := mid) (phiCs.getD 10 0)
    · simpa [accY, accC] using det_const (w := w) (vs := mid) 0
    · simp only [accC, ↓reduceIte, phiB, phiCs, List.map_cons, List.map_nil, CHornerComp,
        List.drop_succ_cons, List.drop_zero]
      apply Complex.ext <;> simp
  | n+1, hn, done, mid, hb, hX, hY, hs => by
    have e : hornerSlots b zx zy (n+1) = hornerSlots b zx zy n ++ hornerSlot b zx zy n := by
      simp [hornerSlots, List.range_succ, List.flatMap_append]
    rw [e] at hs
    obtain ⟨mid0, h1, h2⟩ := slots_append w _ _ _ _ hs
    obtain ⟨⟨L, rfl, hL⟩, hA, hB, hC⟩ := horner_trace n (by omega) done mid0 hb hX hY h1
    obtain ⟨re, hre, im, him, hm⟩ := h2
    have hm : mid = done ++ L ++ [re] ++ [im] := hm
    subst hm
    obtain ⟨p, q, t1, r, s, t2, hp, hq, ht1, hr, hs', ht2, hre', him'⟩ :=
      iter_step (hX.mono L) (hY.mono L) hA hB hre him
    have l0 : (done ++ L).length = b+1+2*n := by simp [hb, hL]
    have g1 : (done ++ L ++ [re] ++ [im]).getD (b+2*(n+1)-1) 0 = re := by
      rw [show b+2*(n+1)-1 = (done ++ L).length by omega]; simp
    have g2 : (done ++ L ++ [re] ++ [im]).getD (b+2*(n+1)) 0 = im := by
      rw [show b+2*(n+1) = (done ++ L ++ [re]).length by simp; omega]; simp
    have hacc : accC b (n+1) (done ++ L ++ [re] ++ [im]) = ⟨re, im⟩ := by
      simp only [accC, Nat.add_one_ne_zero, ↓reduceIte, g1, g2]
    refine ⟨⟨L ++ [re] ++ [im], by simp, by simp [hL]; ring⟩, ?_, ?_, ?_⟩
    · rw [hacc]
      have := det_ref (w := w) (vs := done ++ L ++ [re] ++ [im]) (k := b+2*(n+1)-1)
        (by simp; omega)
      rw [g1] at this
      rwa [show accX b (n+1) = ref (b+2*(n+1)-1) by simp [accX]]
    · rw [hacc]
      have := det_ref (w := w) (vs := done ++ L ++ [re] ++ [im]) (k := b+2*(n+1))
        (by simp; omega)
      rw [g2] at this
      rwa [show accY b (n+1) = ref (b+2*(n+1)) by simp [accY]]
    · obtain ⟨cT', cTs, hd1, hd2⟩ := phiB_drop n (by omega)
      rw [hacc, show 10-(n+1) = 9-n by omega, hd2]
      rw [hd1] at hC
      exact ⟨_, hC, p, q, t1, r, s, t2, re, hp, hq, ht1, hr, hs', ht2, hre', by rw [him']⟩

/-- The trace of the `transfer_phi` slots from `b`, for `z` computed before. -/
theorem phi_trace {w : ℕ → ℝ} {b : ℕ} {zx zy : GExpr} {X Y : ℝ} {done vals : List ℝ}
    (hb : done.length = b) (hX : Det w done zx X) (hY : Det w done zy Y)
    (hs : SlotsComputes w (phiLets b zx zy) done vals) :
    (∃ L, vals = done ++ L ∧ L.length = 24) ∧
    (∃ xx yy, Rnd (X*X) xx ∧ Rnd (Y*Y) yy ∧ Rnd (xx+yy) (vals.getD b 0)) ∧
    CHornerComp ⟨X, Y⟩ phiB ⟨vals.getD (b+19) 0, vals.getD (b+20) 0⟩ ∧
    |vals.getD (b+21) 0-Real.exp (-X)| ≤ (3+2*|X|)*ulp (Real.exp (-X)) ∧
    (∃ o ec, SinCosComputes Y o ∧ Rnd (vals.getD (b+21) 0*o.2) ec ∧
      Rnd (1-ec) (vals.getD (b+22) 0)) ∧
    (∃ o, SinCosComputes Y o ∧ Rnd (vals.getD (b+21) 0*o.1) (vals.getD (b+23) 0)) := by
  obtain ⟨mid1, h01, h3⟩ := slots_append w _ _ _ _ hs
  obtain ⟨m0, h0, h1⟩ := slots_append w _ _ _ _ h01
  obtain ⟨d, hd, hm0⟩ := h0
  have hm0 : m0 = done ++ [d] := hm0
  subst hm0
  obtain ⟨⟨L, rfl, hL⟩, -, -, hC⟩ :=
    horner_trace 10 le_rfl _ mid1 (by simp [hb]) (hX.mono [d]) (hY.mono [d]) h1
  obtain ⟨ev, hev, nx, hnx, ny, hny, hv⟩ := h3
  have hv : vals = done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny] := hv
  subst hv
  have l1 : (done ++ [d] ++ L).length = b+21 := by simp [hb, hL]
  have gd : (done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny]).getD b 0 = d := by
    rw [show b = done.length from hb.symm]; simp
  have gacc (k : ℕ) (hk : k < b+21) :
      (done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny]).getD k 0 = (done ++ [d] ++ L).getD k 0 := by
    have : done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny] = (done ++ [d] ++ L) ++ [ev, nx, ny] := by simp
    rw [this, getD_app _ 0 (by rw [l1]; exact hk)]
  have ge : (done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny]).getD (b+21) 0 = ev := by
    rw [← l1]; simp
  have gnx : (done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny]).getD (b+22) 0 = nx := by
    rw [show b+22 = (done ++ [d] ++ L ++ [ev]).length by simp; omega]; simp
  have gny : (done ++ [d] ++ L ++ [ev] ++ [nx] ++ [ny]).getD (b+23) 0 = ny := by
    rw [show b+23 = (done ++ [d] ++ L ++ [ev] ++ [nx]).length by simp; omega]; simp
  obtain ⟨ya, ⟨yx, hyx, rfl⟩, hexp⟩ := hev
  rw [hX ([d] ++ L) yx (by simpa using hyx)] at hexp
  obtain ⟨one, ec, hone, ⟨e1, c1, he1, ⟨yc, o2, hyc, ho2, rfl⟩, hec⟩, hnx'⟩ := hnx
  obtain ⟨e2, s2, he2, ⟨ys, o1, hys, ho1, rfl⟩, hny'⟩ := hny
  have hone : one = 1 := by have h : one = ((1:ℚ):ℝ) := hone; simpa using h
  have r21 := det_ref (w := w) (vs := done ++ [d] ++ L ++ [ev]) (k := b+21) (by simp; omega)
  have r21' : (done ++ [d] ++ L ++ [ev]).getD (b+21) 0 = ev := by rw [← l1]; simp
  rw [r21'] at r21
  have hyc' : yc = Y := hY ([d] ++ L ++ [ev]) _ (by simpa using hyc)
  have hys' : ys = Y := hY ([d] ++ L ++ [ev] ++ [nx]) _ (by simpa using hys)
  have he1' : e1 = ev := r21 [] _ (by simpa using he1)
  have he2' : e2 = ev := r21 [nx] _ (by simpa using he2)
  rw [hyc'] at ho2
  rw [hys'] at ho1
  rw [he1'] at hec
  rw [he2'] at hny'
  rw [hone] at hnx'
  obtain ⟨xa, yb, ⟨x1, x2, hx1, hx2, hxx⟩, ⟨y1, y2, hy1, hy2, hyy⟩, hdd⟩ := hd
  rw [hX.app hx1, hX.app hx2] at hxx
  rw [hY.app hy1, hY.app hy2] at hyy
  refine ⟨⟨[d] ++ L ++ [ev] ++ [nx] ++ [ny], by simp, by simp [hL]⟩,
    ⟨xa, yb, hxx, hyy, by rw [gd]; exact hdd⟩, ?_, by rw [ge]; simpa using hexp,
    ⟨o2, ec, ho2, by rw [ge]; exact hec, by rw [gnx]; exact hnx'⟩,
    ⟨o1, ho1, by rw [ge, gny]; exact hny'⟩⟩
  rw [gacc _ (by omega), gacc _ (by omega)]
  simpa [accC] using hC

/-- Inputs of `transfer_phi`: `z = (x, y)`. -/
def phiIn (x y : ℝ) (i : ℕ) : ℝ := if i = 0 then x else y

lemma rnd_neg' {a b : ℝ} (h : Rnd a b) : Rnd (-a) (-b) := by
  unfold Rnd at *; rwa [show -b - -a = -(b-a) by ring, abs_neg, abs_neg]

lemma rnd_abs {a b : ℝ} (h : Rnd a b) : |b| ≤ (1+u)*|a|+η := by
  unfold Rnd at h
  have := abs_sub_abs_le_abs_sub b a
  linarith

/-- `φ(z)` in the shader's real arithmetic. -/
lemma phi_parts (x y : ℝ) (hD : x^2+y^2 ≠ 0) :
    (TransferPhi.phi ⟨x, y⟩).re =
      ((1-Real.exp (-x)*Real.cos y)*x+Real.exp (-x)*Real.sin y*y)/(x^2+y^2) ∧
    (TransferPhi.phi ⟨x, y⟩).im =
      (Real.exp (-x)*Real.sin y*x+(-(1-Real.exp (-x)*Real.cos y))*y)/(x^2+y^2) := by
  have hD' : x*x+y*y ≠ 0 := by rwa [← sq, ← sq]
  have hre : (Complex.exp (-(⟨x, y⟩ : ℂ))).re = Real.exp (-x)*Real.cos y := by
    rw [Complex.exp_re]; simp
  have him : (Complex.exp (-(⟨x, y⟩ : ℂ))).im = -(Real.exp (-x)*Real.sin y) := by
    rw [Complex.exp_im]; simp
  unfold TransferPhi.phi
  constructor
  · rw [Complex.div_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
    field_simp
    ring
  · rw [Complex.div_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
    field_simp
    ring

/-- Every computation of the validated `transfer_phi` in which each `let`
value is computed once is within `1200u` of `φ(z)` in each component, for
`0 ≤ Re z ≤ 2⁶²`, `|Im z| ≤ 2¹⁸` and `z ≠ 0`. -/
theorem transfer_phi_slots_error (x y : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 2^62) (hy : |y| ≤ 2^18)
    (hz : (⟨x, y⟩ : ℂ) ≠ 0) (vals : List ℝ)
    (hs : SlotsComputes (phiIn x y) phiProgLets [] vals) (y0 y1 : ℝ)
    (h0 : Computes (env (phiIn x y) vals) (phiProgOut false) y0)
    (h1 : Computes (env (phiIn x y) vals) (phiProgOut true) y1) :
    |y0-(TransferPhi.phi ⟨x, y⟩).re| ≤ 1200*u ∧ |y1-(TransferPhi.phi ⟨x, y⟩).im| ≤ 1200*u := by
  have hu := u_pos
  have hη := η_pos
  set w := phiIn x y
  have hX : Det w [] (input 0) x := by
    simpa [w, phiIn] using det_input (w := w) (vs := []) (i := 0) (by norm_num [letBase])
  have hY : Det w [] (input 1) y := by
    simpa [w, phiIn] using det_input (w := w) (vs := []) (i := 1) (by norm_num [letBase])
  obtain ⟨⟨L, rfl, hL⟩, ⟨xx, yy, hxx, hyy, hd⟩, hC, hexp, ⟨o2, ec, ho2, hec, hnx⟩,
    ⟨o1, ho1, hny⟩⟩ := phi_trace (b := 0) rfl hX hY hs
  simp only [Nat.zero_add] at *
  set d := vals.getD 0 0
  set e := vals.getD 21 0
  set nx := vals.getD 22 0
  set ny := vals.getD 23 0
  have r (k : ℕ) (hk : k < 24) : Det w vals (ref k) (vals.getD k 0) := det_ref (by rw [hL]; exact hk)
  have rx : Det w vals (input 0) x := by simpa using hX.mono vals
  have ry : Det w vals (input 1) y := by simpa using hY.mono vals
  have hD : x^2+y^2 ≠ 0 := by
    intro h
    apply hz
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact Complex.ext (by simp [hx0]) (by simp [hy0])
  obtain ⟨hre, him⟩ := phi_parts x y hD
  have hdom := branch_domains x y xx yy d hxx hyy hd
  simp only [phiProgOut, phiOut, Bool.false_eq_true, ↓reduceIte, Computes] at h0 h1
  obtain ⟨c0, hc0, h0⟩ := h0
  obtain ⟨c1, hc1, h1⟩ := h1
  rw [(r 0 (by norm_num)).app hc0] at h0
  rw [(r 0 (by norm_num)).app hc1] at h1
  have q14 : (((1/4 : ℚ)) : ℝ) = 1/4 := by norm_num
  rw [q14] at h0 h1
  by_cases hsm : d < 1/4
  · -- series branch
    have hy0 : y0 = vals.getD 19 0 := (r 19 (by norm_num)).app (h0.resolve_right (fun h => h.1 hsm)).2
    have hy1 : y1 = vals.getD 20 0 := (r 20 (by norm_num)).app (h1.resolve_right (fun h => h.1 hsm)).2
    have hn2 : ‖(⟨x, y⟩ : ℂ)‖^2 ≤ (5001/10000)^2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith [hdom.1 hsm]
    have hn : ‖(⟨x, y⟩ : ℂ)‖ ≤ 5001/10000 := by nlinarith [norm_nonneg (⟨x, y⟩ : ℂ)]
    have hB : List.Forall₂ (fun c cT => Rnd c cT ∧ |c| ≤ 1) phiCoeffs phiB := by
      simp only [phiCoeffs, phiB, phiCs, List.map_cons, List.map_nil, List.forall₂_cons,
        List.Forall₂.nil, and_true, Rnd, u, η]
      norm_num
    have hser := transfer_phi_series_error _ hz hn phiB hB _ hC
    have hsmall : 33*u+1/10^11 ≤ 1200*u := by norm_num [u]
    constructor
    · rw [hy0]
      have := Complex.abs_re_le_norm ((⟨vals.getD 19 0, vals.getD 20 0⟩ : ℂ)-TransferPhi.phi ⟨x, y⟩)
      simp only [Complex.sub_re] at this
      linarith
    · rw [hy1]
      have := Complex.abs_im_le_norm ((⟨vals.getD 19 0, vals.getD 20 0⟩ : ℂ)-TransferPhi.phi ⟨x, y⟩)
      simp only [Complex.sub_im] at this
      linarith
  · -- direct branch
    have hR := hdom.2 (not_lt.mp hsm)
    have hd14 : 1/4 ≤ d := not_lt.mp hsm
    have hdmax : |d| ≤ 2^126 := by
      have a1 := rnd_abs hxx
      have a2 := rnd_abs hyy
      have a3 := rnd_abs hd
      have hxs : |x*x| ≤ 2^124 := by
        rw [abs_mul, abs_of_nonneg hx]
        calc x*x ≤ 2^62*2^62 := mul_le_mul hx1 hx1 hx (by norm_num)
          _ = 2^124 := by norm_num
      have hys : |y*y| ≤ 2^36 := by
        rw [abs_mul]
        calc |y| *|y| ≤ 2^18*2^18 := mul_le_mul hy hy (abs_nonneg _) (by norm_num)
          _ = 2^36 := by norm_num
      have a4 : |xx+yy| ≤ |xx|+|yy| := abs_add_le _ _
      have hu1 : u ≤ 1 := by norm_num [u]
      have hη1 : η ≤ 1 := by norm_num [η]
      have b1 : |xx| ≤ 2*2^124+1 := by nlinarith
      have b2 : |yy| ≤ 2*2^36+1 := by nlinarith
      have b3 : |xx+yy| ≤ 2*2^124+2*2^36+2 := by linarith
      have hu2 : (1+u)*(2*2^124+2*2^36+2)+1 ≤ (2^126 : ℝ) := by norm_num [u]
      nlinarith [abs_nonneg (xx+yy)]
    have hdiv (num q : ℝ) (hq : DivSpec num d q) : Div num d q :=
      hq ⟨by rw [abs_of_pos (by linarith)]; linarith [show (1:ℝ)/2^126 ≤ 1/4 by norm_num],
        hdmax⟩
    have he : ExpW x e := by
      unfold ExpW
      unfold ulp at hexp
      rw [abs_of_nonneg hx, abs_of_pos (Real.exp_pos _)] at hexp
      calc |e-Real.exp (-x)| ≤ (3+2*x)*(2*u*Real.exp (-x)+η) := hexp
        _ = _ := by ring
    set σ := 128*u*(1+|y|)
    have hσ0 : 0 ≤ σ := by positivity
    have hσ3 : σ ≤ 3 := by
      have : σ ≤ 128*u*(1+2^18) := by
        simp only [σ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : 128*u*(1+2^18) ≤ (3:ℝ) := by norm_num [u]
      linarith
    have hc := (sincos_spec ho2 hy).2
    have hs := (sincos_spec ho1 hy).1
    obtain ⟨hnx', hny'⟩ :=
      direct_numerator x y hx hx1 e o2.2 o1.1 ec nx ny σ he hσ0 hσ3 hc hs hec hnx hny
    have hE0 : 0 < Real.exp (-x) := Real.exp_pos _
    have hE1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hEc : |Real.exp (-x)*Real.cos y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hE0]; nlinarith [Real.abs_cos_le_one y]
    have hEs : |Real.exp (-x)*Real.sin y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hE0]; nlinarith [Real.abs_sin_le_one y]
    have hN1 : |1-Real.exp (-x)*Real.cos y| ≤ 2 := by
      have := abs_sub (1:ℝ) (Real.exp (-x)*Real.cos y); rw [abs_one] at this; linarith
    have h0' := (h0.resolve_left (fun h => hsm h.1)).2
    have h1' := (h1.resolve_left (fun h => hsm h.1)).2
    obtain ⟨num0, d0, ⟨p1, p2, ⟨n1, x1, hn1, hx1', hp1⟩, ⟨n2, y2, hn2, hy2, hp2⟩, hnum⟩, hd0, hq0⟩ := h0'
    rw [(r 22 (by norm_num)).app hn1, rx.app hx1'] at hp1
    rw [(r 23 (by norm_num)).app hn2, ry.app hy2] at hp2
    rw [(r 0 (by norm_num)).app hd0] at hq0
    obtain ⟨num1, d1, ⟨p3, p4, ⟨n3, x3, hn3, hx3, hp3⟩, ⟨n4, y4, hn4, hy4, hp4⟩, hnum1⟩, hd1, hq1⟩ := h1'
    rw [(r 23 (by norm_num)).app hn3, rx.app hx3] at hp3
    rw [(r 22 (by norm_num)).app hn4, ry.app hy4] at hp4
    rw [(r 0 (by norm_num)).app hd1] at hq1
    constructor
    · rw [hre]
      exact direct_component x y hR σ hσ0 le_rfl hy _ _ nx ny x y (Or.inl ⟨rfl, rfl⟩) hN1
        (hEs.trans (by norm_num)) hnx' hny' xx yy d p1 p2 num0 y0 hxx hyy hd hp1 hp2 hnum
        (hdiv _ _ hq0)
    · rw [him]
      have hp4' : Rnd ((-nx)*y) (-p4) := by rw [neg_mul]; exact rnd_neg' hp4
      have hnum1' : Rnd (p3+-p4) num1 := by rwa [← sub_eq_add_neg]
      have hn2' : |-nx-(-(1-Real.exp (-x)*Real.cos y))| ≤ σ+34*u := by
        rw [show -nx-(-(1-Real.exp (-x)*Real.cos y)) = -(nx-(1-Real.exp (-x)*Real.cos y)) by ring,
          abs_neg]
        exact hnx'
      exact direct_component x y hR σ hσ0 le_rfl hy _ _ ny (-nx) x y (Or.inl ⟨rfl, rfl⟩)
        (hEs.trans (by norm_num)) (by rw [abs_neg]; exact hN1) hny' hn2' xx yy d p3 (-p4) num1 y1
        hxx hyy hd hp3 hp4' hnum1' (hdiv _ _ hq1)

end BlackHole.WgslTransferProgram
