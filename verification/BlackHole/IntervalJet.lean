module
public import BlackHole.DyadicInterval
public import BlackHole.NormalizedJet

/-! Soundness of the interval coefficient loops. Every numerical hypothesis
below is an exact dyadic operation check, not an assumed derivative bound. -/

@[expose] public section
noncomputable section
open Set Finset
open scoped Topology
namespace BlackHole.IntervalJet
open DyadicInterval NormalizedJet

def allBelow (N : ℕ) (check : ℕ → Bool) : Bool := (List.range N).all check

theorem allBelow_true (N : ℕ) (check : ℕ → Bool) :
    allBelow N check = true ↔ ∀ k < N, check k = true := by
  simp [allBelow,List.all_eq_true,List.mem_range]

def Encloses (a : ℕ → Bounds) (f : ℝ → ℝ) (N : ℕ) (t : ℝ) : Prop :=
  ∀ k ≤ N, Contains (a k) (coefficient f k t)

def additionCheck (a b c : ℕ → Bounds) (N : ℕ) : Bool :=
  allBelow (N+1) (fun k => addCheck (a k) (b k) (c k))

theorem additionCheck_true (a b c : ℕ → Bounds) (N : ℕ) :
    additionCheck a b c N = true ↔ ∀ k ≤ N, addCheck (a k) (b k) (c k) = true := by
  simp only [additionCheck,allBelow_true,Nat.lt_succ_iff]

theorem add_encloses {a b c : ℕ → Bounds} {f g : ℝ → ℝ} {N : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ N f t) (hg : ContDiffAt ℝ N g t)
    (ha : Encloses a f N t) (hb : Encloses b g N t)
    (hcheck : ∀ k ≤ N, addCheck (a k) (b k) (c k) = true) : Encloses c (f+g) N t := by
  intro k hk
  rw [coefficient_add (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))]
  exact add_sound (hcheck k hk) (ha k hk) (hb k hk)

theorem neg_encloses {a : ℕ → Bounds} {f : ℝ → ℝ} {N : ℕ} {t : ℝ}
    (ha : Encloses a f N t) : Encloses (fun k => negate (a k)) (-f) N t := by
  intro k hk
  rw [coefficient_neg]
  exact neg_sound (ha k hk)

structure ConvolutionRow where
  term : ℕ → Bounds
  accum : ℕ → Bounds

def multiplicationCheck (a b : ℕ → Bounds) (row : ℕ → ConvolutionRow) (N : ℕ) : Bool :=
  allBelow (N+1) fun k => zeroCheck ((row k).accum 0) &&
    allBelow (k+1) (fun i => mulCheck (a i) (b (k-i)) ((row k).term i)) &&
    allBelow (k+1) (fun i => addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1)))

theorem multiplicationCheck_true (a b : ℕ → Bounds) (row : ℕ → ConvolutionRow) (N : ℕ) :
    multiplicationCheck a b row N = true ↔ ∀ k ≤ N,
      zeroCheck ((row k).accum 0) = true ∧
      (∀ i ≤ k, mulCheck (a i) (b (k-i)) ((row k).term i) = true) ∧
      (∀ i ≤ k, addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1)) = true) := by
  simp only [multiplicationCheck,allBelow_true,Nat.lt_succ_iff,Bool.and_eq_true]
  constructor
  · intro h k hk
    obtain ⟨⟨hz,hm⟩,hs⟩ := h k hk
    exact ⟨hz,hm,hs⟩
  · intro h k hk
    obtain ⟨hz,hm,hs⟩ := h k hk
    exact ⟨⟨hz,hm⟩,hs⟩

theorem mul_component {a b : ℕ → Bounds} {f g : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t)
    (ha : Encloses a f n t) (hb : Encloses b g n t) (row : ConvolutionRow)
    (hz : zeroCheck (row.accum 0) = true)
    (hm : ∀ i ≤ n, mulCheck (a i) (b (n-i)) (row.term i) = true)
    (hs : ∀ i ≤ n, addCheck (row.accum i) (row.term i) (row.accum (i+1)) = true) :
    Contains (row.accum (n+1)) (coefficient (f*g) n t) := by
  rw [coefficient_mul hf hg]
  apply sum_sound row.term row.accum _ (n+1) (zero_sound hz)
    (fun i hi => hs i (Nat.le_of_lt_succ hi))
  intro i hi
  have hin := Nat.le_of_lt_succ hi
  exact mul_sound (hm i hin) (ha i hin) (hb (n-i) (Nat.sub_le _ _))

structure QuotientRow extends ConvolutionRow where
  difference : Bounds
  inverse : Bounds

def QuotientChecks (a b c : ℕ → Bounds) (row : ℕ → QuotientRow) (N : ℕ) : Prop :=
  ∀ k ≤ N,
    zeroCheck ((row k).accum 0) = true ∧
    (∀ i < k, mulCheck (b (i+1)) (c (k-(i+1))) ((row k).term i) = true) ∧
    (∀ i < k, addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1)) = true) ∧
    addCheck (a k) (negate ((row k).accum k)) (row k).difference = true ∧
    reciprocalCheck (b 0) (row k).inverse = true ∧
    mulCheck (row k).difference (row k).inverse (c k) = true

def quotientCheck (a b c : ℕ → Bounds) (row : ℕ → QuotientRow) (N : ℕ) : Bool :=
  allBelow (N+1) fun k =>
    zeroCheck ((row k).accum 0) &&
    allBelow k (fun i => mulCheck (b (i+1)) (c (k-(i+1))) ((row k).term i)) &&
    allBelow k (fun i => addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1))) &&
    addCheck (a k) (negate ((row k).accum k)) (row k).difference &&
    reciprocalCheck (b 0) (row k).inverse &&
    mulCheck (row k).difference (row k).inverse (c k)

theorem quotientCheck_true (a b c : ℕ → Bounds) (row : ℕ → QuotientRow) (N : ℕ) :
    quotientCheck a b c row N = true ↔ QuotientChecks a b c row N := by
  simp only [quotientCheck,allBelow_true,Nat.lt_succ_iff,Bool.and_eq_true,QuotientChecks]
  constructor
  · intro h k hk
    obtain ⟨⟨⟨⟨⟨hz,hm⟩,hs⟩,hd⟩,hi⟩,ho⟩ := h k hk
    exact ⟨hz,hm,hs,hd,hi,ho⟩
  · intro h k hk
    obtain ⟨hz,hm,hs,hd,hi,ho⟩ := h k hk
    exact ⟨⟨⟨⟨⟨hz,hm⟩,hs⟩,hd⟩,hi⟩,ho⟩

/-- All division coefficients follow by induction from the checked lower
coefficients; no derivative enclosure for the quotient is an input. -/
theorem div_encloses {a b c : ℕ → Bounds} {f g : ℝ → ℝ} {N : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ N f t) (hg : ContDiffAt ℝ N g t) (hg0 : g t ≠ 0)
    (ha : Encloses a f N t) (hb : Encloses b g N t)
    (row : ℕ → QuotientRow) (hcheck : QuotientChecks a b c row N) :
    Encloses c (fun u => f u/g u) N t := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    obtain ⟨hz,hm,hs,hd,hi,ho⟩ := hcheck k hk
    have hsum : Contains ((row k).accum k)
        (∑ i ∈ range k, coefficient g (i+1) t*
          coefficient (fun u => f u/g u) (k-(i+1)) t) := by
      apply sum_sound (row k).term (row k).accum _ k (zero_sound hz) hs
      intro i hik
      exact mul_sound (hm i hik) (hb (i+1) (by omega))
        (ih (k-(i+1)) (by omega) (by omega))
    have hdiff := sub_sound hd (ha k hk) hsum
    have hinv := reciprocal_sound hi (hb 0 (Nat.zero_le N))
    simp only [coefficient_zero] at hinv
    have hout := mul_sound ho hdiff hinv
    rw [coefficient_div (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk)) hg0]
    simpa only [div_eq_mul_inv,one_div,one_mul] using hout

structure RootRow extends QuotientRow where
  denominator : Bounds

def two : Bounds := ⟨2,2⟩

theorem two_contains : Contains two 2 := by
  simp [Contains,two]

def RootChecks (a c : ℕ → Bounds) (row : ℕ → RootRow) (N : ℕ) : Prop :=
  sqrtCheck (a 0) (c 0) = true ∧ ∀ k < N,
    zeroCheck ((row k).accum 0) = true ∧
    (∀ i < k, mulCheck (c (i+1)) (c (k-i)) ((row k).term i) = true) ∧
    (∀ i < k, addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1)) = true) ∧
    addCheck (a (k+1)) (negate ((row k).accum k)) (row k).difference = true ∧
    mulCheck two (c 0) (row k).denominator = true ∧
    reciprocalCheck (row k).denominator (row k).inverse = true ∧
    mulCheck (row k).difference (row k).inverse (c (k+1)) = true

def rootCheck (a c : ℕ → Bounds) (row : ℕ → RootRow) (N : ℕ) : Bool :=
  sqrtCheck (a 0) (c 0) && allBelow N (fun k =>
    zeroCheck ((row k).accum 0) &&
    allBelow k (fun i => mulCheck (c (i+1)) (c (k-i)) ((row k).term i)) &&
    allBelow k (fun i => addCheck ((row k).accum i) ((row k).term i) ((row k).accum (i+1))) &&
    addCheck (a (k+1)) (negate ((row k).accum k)) (row k).difference &&
    mulCheck two (c 0) (row k).denominator &&
    reciprocalCheck (row k).denominator (row k).inverse &&
    mulCheck (row k).difference (row k).inverse (c (k+1)))

theorem rootCheck_true (a c : ℕ → Bounds) (row : ℕ → RootRow) (N : ℕ) :
    rootCheck a c row N = true ↔ RootChecks a c row N := by
  simp only [rootCheck,allBelow_true,Bool.and_eq_true,RootChecks]
  constructor
  · rintro ⟨hzero,h⟩
    refine ⟨hzero,fun k hk => ?_⟩
    obtain ⟨⟨⟨⟨⟨⟨hz,hm⟩,hs⟩,hd⟩,hmden⟩,hi⟩,ho⟩ := h k hk
    exact ⟨hz,hm,hs,hd,hmden,hi,ho⟩
  · rintro ⟨hzero,h⟩
    refine ⟨hzero,fun k hk => ?_⟩
    obtain ⟨hz,hm,hs,hd,hmden,hi,ho⟩ := h k hk
    exact ⟨⟨⟨⟨⟨⟨hz,hm⟩,hs⟩,hd⟩,hmden⟩,hi⟩,ho⟩

/-- Square-root enclosures include every computed coefficient's rounding. -/
theorem sqrt_encloses {a c : ℕ → Bounds} {f : ℝ → ℝ} {N : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ N f t) (hpos : 0 < f t) (ha : Encloses a f N t)
    (row : ℕ → RootRow) (hcheck : RootChecks a c row N) :
    Encloses c (fun u => Real.sqrt (f u)) N t := by
  have hbase : Contains (c 0) (Real.sqrt (f t)) := by
    have := sqrt_sound hcheck.1 (ha 0 (Nat.zero_le N))
    simpa only [coefficient_zero] using this
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => simpa only [coefficient_zero] using hbase
    | succ k =>
      obtain ⟨hz,hm,hs,hd,hmden,hi,ho⟩ := hcheck.2 k (by omega)
      have hsum : Contains ((row k).accum k)
          (∑ i ∈ range k, coefficient (fun u => Real.sqrt (f u)) (i+1) t*
            coefficient (fun u => Real.sqrt (f u)) (k-i) t) := by
        apply sum_sound (row k).term (row k).accum _ k (zero_sound hz) hs
        intro i hik
        exact mul_sound (hm i hik) (ih (i+1) (by omega) (by omega))
          (ih (k-i) (by omega) (by omega))
      have hdiff := sub_sound hd (ha (k+1) hk) hsum
      have hden := mul_sound hmden two_contains hbase
      have hout := mul_sound ho hdiff (reciprocal_sound hi hden)
      rw [coefficient_sqrt (hf.of_le (by exact_mod_cast hk)) hpos]
      simpa only [div_eq_mul_inv,one_div,one_mul] using hout

end BlackHole.IntervalJet
