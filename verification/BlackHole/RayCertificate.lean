module
public import BlackHole.CameraPhysics

/-! The end-to-end certified ray. `certify` checks camera initialization,
every step, the event classification and (for an escape) the observables.
`certified_ray` states what success means for the exact Kerr ray from the
camera: it exists over the whole certified affine interval, every solution
of the full eleven-component equations that stays where they are defined
satisfies the verdict, and an escaping ray's observables meet the targets. -/

@[expose] public section
open Set
namespace BlackHole.RayCertificate
open DyadicInterval KerrProgram StepField StepCheck TraceCheck RayEvents RayObserve

structure Report where
  pt : Bounds
  initial : Fin 10 → Bounds
  results : List Result
  verdict : Verdict

def certify (prec : ℕ) (spin pos dir hint : Fin 3 → Dyadic) (steps : List Step)
    (observation : Observation) : Option Report := do
  require (CameraPhysics.cameraChecks spin pos dir hint prec)
  let (PT,X) ← cameraBoxes prec spin pos dir hint
  let (rs,v) ← checkTrace prec spin PT X steps
  let last ← rs.getLast?
  require (v != .escaped || observe prec spin PT last.final observation)
  pure ⟨PT,X,rs,v⟩

noncomputable section

def drop (Z : KerrField.Phase) : Reduced := fun i => phaseGet Z (component i)

theorem full_drop (Z : KerrField.Phase) : full (Z.2.1 0) (drop Z) = Z := by
  obtain ⟨x,p,f⟩ := Z
  simp only [full,toPhase,assemble,drop]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; fin_cases i <;> rfl
  · funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem drop_full (pt : ℝ) (y : Reduced) : drop (full pt y) = y := by
  funext i; fin_cases i <;> rfl

theorem full_pt (pt : ℝ) (y : Reduced) : (full pt y).2.1 0 = pt := rfl

/-- A solution of all eleven equations keeps its time momentum and solves
the reduced system with that parameter. -/
theorem reduce_solution (a : Cartesian.Space) (D : ℝ) (Z : ℝ → KerrField.Phase)
    (hZ : ∀ t ∈ Icc 0 D, HasDerivWithinAt Z (KerrField.phaseRhs 1 a (Z t)) (Icc 0 D) t) :
    (∀ t ∈ Icc 0 D, (Z t).2.1 0 = (Z 0).2.1 0) ∧
      Solves a ((Z 0).2.1 0) (fun t => drop (Z t)) D := by
  have hcomp (c : Component) (t : ℝ) (ht : t ∈ Icc 0 D) :
      HasDerivWithinAt (fun u => phaseGet (Z u) c) (phaseGet (KerrField.phaseRhs 1 a (Z t)) c) (Icc 0 D) t := by
    have h := hZ t ht
    cases c with
    | position i => exact hasDerivWithinAt_pi.mp h.fst i
    | momentum i => exact hasDerivWithinAt_pi.mp h.snd.fst i
    | screen i => exact hasDerivWithinAt_pi.mp h.snd.snd i
  by_cases hD : 0 ≤ D
  swap
  · simp [Icc_eq_empty (by linarith : ¬ (0:ℝ) ≤ D),Solves]
  have hconst : ∀ t ∈ Icc 0 D, (Z t).2.1 0 = (Z 0).2.1 0 := by
    apply constant_of_has_deriv_right_zero
    · exact HasDerivWithinAt.continuousOn fun t ht => hcomp (.momentum 0) t ht
    · intro t ht
      have h := (hcomp (.momentum 0) t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
      simpa [phaseGet,KerrField.phase_rhs_stationary] using h
  refine ⟨hconst,fun t ht => ?_⟩
  have hZt : full ((Z 0).2.1 0) (drop (Z t)) = Z t := by rw [← hconst t ht,full_drop]
  refine hasDerivWithinAt_pi.mpr fun i => ?_
  simp only [field,hZt]
  exact hcomp (component i) t ht

def cameraPhase (spin pos dir hint : Fin 3 → Dyadic) : KerrField.Phase :=
  full (cameraPt spin pos dir realOperations) (cameraY spin pos dir hint realOperations)

theorem follows_domain (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) :
    ∀ (steps : List Step) (rs : List Result) (t0 : ℝ), steps ≠ [] → Follows a pt z steps rs t0 →
      ∀ t ∈ Icc t0 (t0+duration steps), 0 < Cartesian.radius a (full pt (z t)).1
  | [],_,_,h,_ => absurd rfl h
  | [s],[r],t0,_,hF => by
    simp only [Follows,duration,add_zero] at hF ⊢
    exact fun t ht => (hF.1 t ht).2
  | s :: s' :: rest,r :: rs,t0,_,hF => by
    simp only [Follows] at hF
    intro t ht
    by_cases hts : t ≤ t0+s.h.toReal
    · exact (hF.1 t ⟨ht.1,hts⟩).2
    · exact follows_domain a pt z (s' :: rest) rs _ (by simp) hF.2.2 t
        ⟨by linarith,by simp only [duration] at ht ⊢; linarith [ht.2]⟩
  | [_],[],_,_,hF => hF.elim
  | [_],_ :: _ :: _,_,_,hF => by simp [Follows] at hF
  | _ :: _ :: _,[],_,_,hF => hF.elim

theorem follows_last (a : Cartesian.Space) (pt : ℝ) (z : ℝ → Reduced) :
    ∀ (steps : List Step) (rs : List Result) (t0 : ℝ) (last : Result), rs.getLast? = some last →
      Follows a pt z steps rs t0 → ∀ i, Contains (last.final i) (z (t0+duration steps) i)
  | [],[],_,_,h,_ => by simp at h
  | [s],[r],t0,last,h,hF => by
    simp only [List.getLast?_singleton,Option.some.injEq] at h
    subst h
    simp only [Follows,duration,add_zero] at hF ⊢
    exact hF.2.1
  | s :: s' :: rest,r :: r' :: rs,t0,last,h,hF => by
    simp only [Follows] at hF
    have h' : (r' :: rs).getLast? = some last := by
      rw [List.getLast?_cons_cons] at h; exact h
    have := follows_last a pt z (s' :: rest) (r' :: rs) _ last h' hF.2.2
    simpa [duration,add_assoc] using this
  | [],_ :: _,_,_,_,hF => hF.elim
  | _ :: _,[],_,_,_,hF => hF.elim
  | [_],_ :: _ :: _,_,_,_,hF => by simp [Follows] at hF
  | _ :: _ :: _,[_],_,_,_,hF => by simp [Follows] at hF

/-- What a successful certificate means for the exact ray from the camera. -/
theorem certified_ray (prec : ℕ) (spin pos dir hint : Fin 3 → Dyadic) (steps : List Step)
    (observation : Observation) (report : Report)
    (h : certify prec spin pos dir hint steps observation = some report) :
    let a := CheckedFunction.spinValue spin
    let D := duration steps
    (let p := cameraMomentum spin pos dir realOperations
     let f : Fin 4 → ℝ := Fin.cases 0 (cameraScreen spin pos dir hint realOperations)
     let inv := (CameraPhysics.G spin pos)⁻¹
     dotProduct (inv.mulVec p) p = 0 ∧ dotProduct p (ADM.observer inv) = 1 ∧ 0 < ADM.observer inv 0 ∧
       dotProduct f ((CameraPhysics.G spin pos).mulVec f) = 1 ∧ dotProduct p f = 0) ∧
    (∃ Z : ℝ → KerrField.Phase, Z 0 = cameraPhase spin pos dir hint ∧
      ∀ t ∈ Icc 0 D, HasDerivWithinAt Z (KerrField.phaseRhs 1 a (Z t)) (Icc 0 D) t ∧
        0 < Cartesian.radius a (Z t).1) ∧
    ∀ Z : ℝ → KerrField.Phase, Z 0 = cameraPhase spin pos dir hint →
      (∀ t ∈ Icc 0 D, HasDerivWithinAt Z (KerrField.phaseRhs 1 a (Z t)) (Icc 0 D) t) →
      (∀ t ∈ Icc 0 D, 0 < Cartesian.radius a (Z t).1) →
      (∀ t ∈ Icc 0 D, Throughout a ((Z t).2.1 0) (drop (Z t)) report.verdict) ∧
      AtEnd a ((Z D).2.1 0) (drop (Z D)) report.verdict ∧
      (∀ last ∈ report.results.getLast?, ∀ i, Contains (last.final i) (drop (Z D) i)) ∧
      (report.verdict = .escaped →
        let v := fullVec ((Z D).2.1 0) (drop (Z D))
        InnerProductGeometry.angle (realDirection spin v) (unitOut observation.direction) ≤ 1/1000000 ∧
        0 < redshiftP spin realOperations v ∧
        |observation.redshift.toReal-redshiftP spin realOperations v| ≤ redshiftP spin realOperations v/1000000 ∧
        |screenNormP spin realOperations v| ≤ 1/1000000 ∧
        |transversalityP realOperations v| ≤ 1/1000000) := by
  intro a D
  simp only [certify,bind,Option.bind_eq_some_iff,pure,Option.some.injEq] at h
  obtain ⟨u0,hu0,⟨PT,X⟩,hcam,⟨rs,v⟩,htr,last,hlast,u,hu,rfl⟩ := h
  obtain ⟨hr0,hd0,hs0⟩ := CameraPhysics.cameraChecks_sound spin pos dir hint prec (require_some hu0)
  have hobs := require_some hu
  obtain ⟨hpt,hX⟩ := cameraBoxes_sound prec spin pos dir hint PT X hcam
  set pt := cameraPt spin pos dir realOperations
  set y0 := cameraY spin pos dir hint realOperations
  have hrs := checkTrace_steps prec spin PT X steps (rs,v) htr
  have hne : steps ≠ [] := by
    rintro rfl; simp [checkTrace] at htr
  have hrsne : rs ≠ [] := by rintro rfl; simp at hlast
  refine ⟨CameraPhysics.camera_physics spin pos dir hint hr0 hd0 hs0,?_,?_⟩
  · obtain ⟨z,hz0,hzs,hzF⟩ := steps_exist prec spin PT pt hpt X steps rs hrs y0 hX
    have hdom := follows_domain a pt z steps rs 0 hne hzF
    refine ⟨fun t => full pt (z t),by simp [cameraPhase,hz0,pt,y0],fun t ht => ⟨?_,?_⟩⟩
    · exact lift a pt z _ t (hzs t ht)
    · simpa using hdom t (by simpa using ht)
  · intro Z hZ0 hZ hZU
    obtain ⟨hconst,hred⟩ := reduce_solution a D Z hZ
    have hpt0 : (Z 0).2.1 0 = pt := by rw [hZ0]; rfl
    rw [hpt0] at hconst hred
    have hy0 : drop (Z 0) = y0 := by rw [hZ0]; exact drop_full pt y0
    have hU : InDomain a pt (fun t => drop (Z t)) D := by
      intro t ht
      have : full pt (drop (Z t)) = Z t := by rw [← hconst t ht,full_drop]
      rw [this]; exact hZU t ht
    have hX' : ∀ i, Contains (X i) (drop (Z 0) i) := by rw [hy0]; exact hX
    have hT := trace_sound prec spin PT pt hpt X steps (rs,v) htr _ hX' hred hU
    have hD0 : 0 ≤ D := duration_nonneg X steps rs hrs
    have hptD : (Z D).2.1 0 = pt := hconst D ⟨hD0,le_rfl⟩
    have hF := steps_unique prec spin PT pt hpt X steps rs hrs _ hX' hred hU
    have hfin := follows_last a pt _ steps rs 0 last hlast hF
    simp only [zero_add] at hfin
    refine ⟨fun t ht => ?_,?_,fun l hl i => ?_,fun hesc => ?_⟩
    · rw [hconst t ht]; exact hT.1 t ht
    · rw [hptD]; exact hT.2
    · have hl' : l = last := by rw [hlast] at hl; exact (Option.mem_some_iff.mp hl).symm
      subst hl'
      exact hfin i
    · have hsel : observe prec spin PT last.final observation = true := by
        simp only [bne_iff_ne,ne_eq,Bool.or_eq_true] at hobs
        rcases hobs with h1 | h1
        · exact absurd hesc h1
        · exact h1
      rw [hptD]
      exact observe_sound prec spin PT last.final observation hsel pt hpt _ hfin

end

end BlackHole.RayCertificate
