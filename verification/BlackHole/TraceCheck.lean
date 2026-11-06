module
public import BlackHole.StepCheck

/-! Chained step certificates. `steps_exist` glues the certified segments
into one exact solution over the whole affine interval, and `steps_unique`
shows that every solution staying where the equations are defined follows
the same tubes. Together they describe the exact ray, not just some curve. -/

@[expose] public section
open Set
open scoped Topology NNReal
namespace BlackHole.TraceCheck
open DyadicInterval StepField StepCheck

def checkSteps (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) :
    (Fin 10 → Bounds) → List Step → Option (List Result)
  | _, [] => some []
  | X, s :: rest => do
    let r ← check prec spin PT X s
    let rs ← checkSteps prec spin PT r.final rest
    pure (r :: rs)

noncomputable section

def duration : List Step → ℝ
  | [] => 0
  | s :: rest => s.h.toReal+duration rest

def Solves (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) (D : ℝ) : Prop :=
  ∀ t ∈ Icc 0 D, HasDerivWithinAt z (field a pt (z t)) (Icc 0 D) t

def InDomain (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) (D : ℝ) : Prop :=
  ∀ t ∈ Icc 0 D, 0 < Cartesian.radius a (full pt (z t)).1

/-- The curve follows the certified tubes and step-end boxes, starting at `t0`. -/
def Follows (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) : List Step → List Result → ℝ → Prop
  | [],[],_ => True
  | s :: ss,r :: rs,t0 =>
    (∀ t ∈ Icc t0 (t0+s.h.toReal), (∀ i, Contains (r.tube i) (z t i)) ∧
      0 < Cartesian.radius a (full pt (z t)).1) ∧
    (∀ i, Contains (r.final i) (z (t0+s.h.toReal) i)) ∧ Follows a pt z ss rs (t0+s.h.toReal)
  | _,_,_ => False

theorem follows_shift (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) (c : ℝ) :
    ∀ (ss : List Step) (rs : List Result) (t0 : ℝ),
      Follows a pt (fun t => z (t+c)) ss rs t0 ↔ Follows a pt z ss rs (t0+c)
  | [],[],_ => Iff.rfl
  | [],_ :: _,_ => Iff.rfl
  | _ :: _,[],_ => Iff.rfl
  | s :: ss,r :: rs,t0 => by
    simp only [Follows]
    rw [follows_shift a pt z c ss rs,show t0+s.h.toReal+c = t0+c+s.h.toReal by ring]
    constructor
    · rintro ⟨h1,h2,h3⟩
      refine ⟨fun t ht => ?_,h2,h3⟩
      have := h1 (t-c) ⟨by linarith [ht.1],by linarith [ht.2]⟩
      simpa using this
    · rintro ⟨h1,h2,h3⟩
      exact ⟨fun t ht => h1 (t+c) ⟨by linarith [ht.1],by linarith [ht.2]⟩,h2,h3⟩

theorem follows_congr (a : Cartesian.Space) (pt : ℝ) (f g : ℝ → Reduced) :
    ∀ (ss : List Step) (rs : List Result) (t0 : ℝ), (∀ s ∈ ss, 0 ≤ s.h.toReal) →
      (∀ t ≥ t0, f t = g t) → (Follows a pt f ss rs t0 ↔ Follows a pt g ss rs t0)
  | [],[],_,_,_ => Iff.rfl
  | [],_ :: _,_,_,_ => Iff.rfl
  | _ :: _,[],_,_,_ => Iff.rfl
  | s :: ss,r :: rs,t0,hpos,h => by
    have h0 := hpos s (List.mem_cons_self ..)
    have hrest := follows_congr a pt f g ss rs (t0+s.h.toReal)
      (fun s' hs' => hpos s' (List.mem_cons_of_mem _ hs')) (fun t ht => h t (by linarith))
    simp only [Follows,hrest,h (t0+s.h.toReal) (by linarith)]
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨fun t ht => by rw [← h t ht.1]; exact h1 t ht,h2,h3⟩
    · rintro ⟨h1,h2,h3⟩
      exact ⟨fun t ht => by rw [h t ht.1]; exact h1 t ht,h2,h3⟩

theorem check_positive {prec : ℕ} {spin : Fin 3 → Dyadic} {PT : Bounds} {X : Fin 10 → Bounds}
    {s : Step} {r : Result} (h : check prec spin PT X s = some r) : 0 < s.h.toReal := by
  simp only [check,bind,Option.bind_eq_some_iff] at h
  obtain ⟨u,hu,-⟩ := h
  have b := require_some hu
  simp only [Bool.and_eq_true,decide_eq_true_eq] at b
  simpa using Dyadic.toReal_lt_toReal.mpr b.1.1

theorem checkSteps_cons {prec : ℕ} {spin : Fin 3 → Dyadic} {PT : Bounds} {X : Fin 10 → Bounds}
    {s : Step} {rest : List Step} {rs : List Result}
    (h : checkSteps prec spin PT X (s :: rest) = some rs) :
    ∃ r rs', check prec spin PT X s = some r ∧ checkSteps prec spin PT r.final rest = some rs' ∧
      rs = r :: rs' := by
  simp only [checkSteps,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
  obtain ⟨r,hr,rs',hrs,rfl⟩ := h
  exact ⟨r,rs',hr,hrs,rfl⟩

theorem checkSteps_positive {prec : ℕ} {spin : Fin 3 → Dyadic} {PT : Bounds} :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (rs : List Result),
      checkSteps prec spin PT X steps = some rs → ∀ s ∈ steps, 0 < s.h.toReal
  | _,[],_,_ => by simp
  | X,s :: rest,rs,h => by
    obtain ⟨r,rs',hr,hrs,-⟩ := checkSteps_cons h
    intro s' hs'
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact check_positive hr
    · exact checkSteps_positive _ rest rs' hrs s' hs'

theorem duration_nonneg {prec : ℕ} {spin : Fin 3 → Dyadic} {PT : Bounds} :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (rs : List Result),
      checkSteps prec spin PT X steps = some rs → 0 ≤ duration steps
  | _,[],_,_ => le_rfl
  | X,s :: rest,rs,h => by
    obtain ⟨r,rs',hr,hrs,-⟩ := checkSteps_cons h
    exact add_nonneg (check_positive hr).le (duration_nonneg _ rest rs' hrs)

theorem field_locallyLipschitz (a : Cartesian.Space) (pt : ℝ) :
    LocallyLipschitzOn {y : Reduced | 0 < Cartesian.radius a (full pt y).1} (field a pt) := by
  intro y hy
  obtain ⟨K,t,ht,hK⟩ := ((field_smooth a pt y hy).of_le (by simp)).exists_lipschitzOnWith
  exact ⟨K,t,mem_nhdsWithin_of_mem_nhds ht,hK⟩

/-- Two solutions that stay where the Kerr equations are defined coincide. -/
theorem solution_unique (a : Cartesian.Space) (pt T : ℝ) (y z : ℝ → Reduced)
    (hy : Solves a pt y T) (hz : Solves a pt z T)
    (hyU : InDomain a pt y T) (hzU : InDomain a pt z T) (h0 : y 0 = z 0) :
    EqOn y z (Icc 0 T) := by
  have hyc : ContinuousOn y (Icc 0 T) := HasDerivWithinAt.continuousOn hy
  have hzc : ContinuousOn z (Icc 0 T) := HasDerivWithinAt.continuousOn hz
  set K := y '' Icc 0 T ∪ z '' Icc 0 T
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hyc).union
    (isCompact_Icc.image_of_continuousOn hzc)
  have hsub : K ⊆ {y : Reduced | 0 < Cartesian.radius a (full pt y).1} := by
    rintro _ (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · exact hyU t ht
    · exact hzU t ht
  obtain ⟨L,hL⟩ := ((field_locallyLipschitz a pt).mono hsub).exists_lipschitzOnWith_of_compact hK
  have hright (f : ℝ → Reduced) (hf : Solves a pt f T) (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt f (field a pt (f t)) (Ici t) t :=
    (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => field a pt) (s := fun _ => K) (K := L)
    (fun _ _ => hL) hyc (hright y hy) (fun t ht => Or.inl ⟨t,Ico_subset_Icc_self ht,rfl⟩)
    hzc (hright z hz) (fun t ht => Or.inr ⟨t,Ico_subset_Icc_self ht,rfl⟩) h0

theorem solves_shift (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) (h D : ℝ) (hh : 0 ≤ h)
    (hz : Solves a pt z (h+D)) : Solves a pt (fun t => z (t+h)) D := by
  intro t ht
  have hm : t+h ∈ Icc 0 (h+D) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hmaps : MapsTo (fun u => id u+h) (Icc 0 D) (Icc 0 (h+D)) :=
    fun u hu => ⟨by simp; linarith [hu.1],by simp; linarith [hu.2]⟩
  have hd := (hz (t+h) hm).scomp t ((hasDerivAt_id t).add_const h).hasDerivWithinAt hmaps
  simpa [Function.comp_def] using hd

/-- Every exact solution that stays in the domain follows the certified tubes. -/
theorem steps_unique (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (pt : ℝ) (hpt : Contains PT pt) :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (rs : List Result),
      checkSteps prec spin PT X steps = some rs →
      ∀ z : ℝ → Reduced, (∀ i, Contains (X i) (z 0 i)) →
        Solves (CheckedFunction.spinValue spin) pt z (duration steps) →
        InDomain (CheckedFunction.spinValue spin) pt z (duration steps) →
        Follows (CheckedFunction.spinValue spin) pt z steps rs 0
  | _,[],rs,h,_,_,_,_ => by
    simp only [checkSteps,Option.some.injEq] at h
    subst h; trivial
  | X,s :: rest,rs,h,z,hz0,hz,hzU => by
    obtain ⟨r,rs',hr,hrs,rfl⟩ := checkSteps_cons h
    have hh := check_positive hr
    have hD := duration_nonneg _ rest rs' hrs
    obtain ⟨y,hy0,hyd,hyT,hyU,hyF⟩ := check_sound prec spin PT X s r hr pt hpt (z 0) hz0
    have hsub : Icc 0 s.h.toReal ⊆ Icc 0 (duration (s :: rest)) :=
      Icc_subset_Icc le_rfl (by simp [duration]; linarith)
    have heq := solution_unique _ pt s.h.toReal y z hyd
      (fun t ht => (hz t (hsub ht)).mono hsub) hyU (fun t ht => hzU t (hsub ht)) hy0
    have hend : z s.h.toReal = y s.h.toReal := (heq ⟨hh.le,le_rfl⟩).symm
    have htail := steps_unique prec spin PT pt hpt r.final rest rs' hrs (fun t => z (t+s.h.toReal))
      (fun i => by simpa [hend] using hyF i)
      (solves_shift _ pt z _ _ hh.le (by simpa [duration] using hz))
      (fun t ht => hzU (t+s.h.toReal) ⟨by linarith [ht.1],by simp [duration]; linarith [ht.2]⟩)
    rw [follows_shift] at htail
    simp only [Follows,zero_add] at htail ⊢
    refine ⟨fun t ht => ?_,fun i => ?_,htail⟩
    · rw [← heq ht]; exact ⟨hyT t ht,hyU t ht⟩
    · rw [hend]; exact hyF i

theorem solves_glue (a : Cartesian.Space) (pt : ℝ) (y z : ℝ → Reduced) (h D : ℝ) (hh : 0 ≤ h)
    (hD : 0 ≤ D) (hy : Solves a pt y h) (hz : Solves a pt z D) (hjoin : y h = z 0) :
    Solves a pt (fun t => if t ≤ h then y t else z (t-h)) (h+D) := by
  set g := fun t => if t ≤ h then y t else z (t-h)
  have hleft : ∀ t ∈ Icc 0 h, HasDerivWithinAt g (field a pt (g t)) (Icc 0 h) t := by
    intro t ht
    have hg : g t = y t := by simp [g,ht.2]
    rw [hg]
    exact (hy t ht).congr (fun u hu => by simp [g,hu.2]) hg
  have hright : ∀ t ∈ Icc h (h+D), HasDerivWithinAt g (field a pt (g t)) (Icc h (h+D)) t := by
    intro t ht
    have hval (u : ℝ) (hu : u ∈ Icc h (h+D)) : g u = z (u-h) := by
      by_cases hu' : u ≤ h
      · have : u = h := le_antisymm hu' hu.1
        simp [g,this,hjoin]
      · simp [g,hu']
    rw [hval t ht]
    have hm : t-h ∈ Icc 0 D := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hmaps : MapsTo (fun u => id u-h) (Icc h (h+D)) (Icc 0 D) :=
      fun u hu => ⟨by simp; linarith [hu.1],by simp; linarith [hu.2]⟩
    have hd := (hz (t-h) hm).scomp t ((hasDerivAt_id t).sub_const h).hasDerivWithinAt hmaps
    exact (by simpa [Function.comp_def] using hd :
      HasDerivWithinAt (fun u => z (u-h)) (field a pt (z (t-h))) (Icc h (h+D)) t).congr
      (fun u hu => hval u hu) (hval t ht)
  intro t ht
  rcases lt_trichotomy t h with h1 | h1 | h1
  · refine (hleft t ⟨ht.1,h1.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Iio h,isOpen_Iio,h1,fun u hu => ⟨hu.2.1,le_of_lt hu.1⟩⟩)
  · subst h1
    have hu := (hleft t ⟨ht.1,le_rfl⟩).union (hright t ⟨le_rfl,by linarith⟩)
    rwa [Icc_union_Icc_eq_Icc hh (by linarith)] at hu
  · refine (hright t ⟨h1.le,ht.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Ioi h,isOpen_Ioi,h1,fun u hu => ⟨le_of_lt hu.1,hu.2.2⟩⟩)

/-- The certified segments glue into one exact solution over the whole
affine interval, for every initial point and time momentum in the boxes. -/
theorem steps_exist (prec : ℕ) (spin : Fin 3 → Dyadic) (PT : Bounds) (pt : ℝ) (hpt : Contains PT pt) :
    ∀ (X : Fin 10 → Bounds) (steps : List Step) (rs : List Result),
      checkSteps prec spin PT X steps = some rs →
      ∀ x : Reduced, (∀ i, Contains (X i) (x i)) →
        ∃ z : ℝ → Reduced, z 0 = x ∧ Solves (CheckedFunction.spinValue spin) pt z (duration steps) ∧
          Follows (CheckedFunction.spinValue spin) pt z steps rs 0
  | _,[],rs,h,x,_ => by
    simp only [checkSteps,Option.some.injEq] at h
    subst h
    refine ⟨fun _ => x,rfl,fun t ht => ?_,trivial⟩
    have hI : Icc (0:ℝ) (duration []) = {0} := by simp [duration]
    rw [hI] at ht ⊢
    rw [mem_singleton_iff.mp ht]
    refine HasFDerivWithinAt.of_not_accPt ?_
    rw [accPt_iff_nhds]
    simp
    exact ⟨_,Filter.univ_mem⟩
  | X,s :: rest,rs,h,x,hx => by
    obtain ⟨r,rs',hr,hrs,rfl⟩ := checkSteps_cons h
    have hh := check_positive hr
    have hD := duration_nonneg _ rest rs' hrs
    obtain ⟨y,hy0,hyd,hyT,hyU,hyF⟩ := check_sound prec spin PT X s r hr pt hpt x hx
    obtain ⟨z,hz0,hzd,hzF⟩ := steps_exist prec spin PT pt hpt r.final rest rs' hrs (y s.h.toReal) hyF
    refine ⟨fun t => if t ≤ s.h.toReal then y t else z (t-s.h.toReal),by simp [hy0,hh.le],?_,?_⟩
    · simpa [duration] using solves_glue _ pt y z _ _ hh.le hD hyd hzd hz0.symm
    · have hval : ∀ t ≥ s.h.toReal,
          (fun t => if t ≤ s.h.toReal then y t else z (t-s.h.toReal)) t = z (t+-s.h.toReal) := by
        intro t ht
        by_cases h' : t ≤ s.h.toReal
        · have : t = s.h.toReal := le_antisymm h' ht
          simp [this,hz0]
        · simp [h',sub_eq_add_neg]
      have hshift := (follows_shift _ pt z (-s.h.toReal) rest rs' s.h.toReal).mpr (by simpa using hzF)
      have htail := (follows_congr _ pt _ _ rest rs' s.h.toReal
        (fun s' hs' => (checkSteps_positive _ rest rs' hrs s' hs').le) hval).mpr hshift
      simp only [Follows,zero_add]
      refine ⟨fun t ht => ?_,fun i => ?_,htail⟩
      · simp only [ht.2,↓reduceIte]; exact ⟨hyT t ht,hyU t ht⟩
      · simp only [le_refl,↓reduceIte]; exact hyF i

end

end BlackHole.TraceCheck