module
public import BlackHole.KerrCompact
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Cauchy

/-! Finite-time continuation for the exact Kerr geodesic/screen ODE (N2).
A trajectory remaining in a compact nonsingular phase region has a regular
endpoint and extends past every finite endpoint. Leaving the region, capture,
and discrete or floating-point execution are separate obligations. -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace BlackHole.KerrField

theorem compact_endpoint (mass : ℝ) (a : Cartesian.Space) {s : Set Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1)
    (curve : ℝ → Phase) (T : ℝ) (hT : 0 < T)
    (hsol : ∀ t ∈ Ioo 0 T, HasDerivAt curve (phaseRhs mass a (curve t)) t)
    (hmem : ∀ t ∈ Ioo 0 T, curve t ∈ s) :
    ∃ y ∈ s, Tendsto curve (𝓝[<] T) (𝓝 y) := by
  obtain ⟨M,hM,hb⟩ := phase_rhs_derivatives_bounded mass a hs hr 0
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 T) : ‖phaseRhs mass a (curve t)‖ ≤ M :=
    by simpa only [norm_iteratedFDeriv_zero] using hb (curve t) (hmem t ht)
  have hlip (u v : ℝ) (hu : u ∈ Ioo 0 T) (hv : v ∈ Ioo 0 T) :
      dist (curve u) (curve v) ≤ M*|u-v| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using
      (convex_Ioo (0:ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht => (hsol t ht).hasDerivWithinAt) hbound hv hu
  have hcf : Cauchy (Filter.map curve (𝓝[<] T)) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance,fun ε hε => ?_⟩
    let δ := ε/(M+1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let I := Ioo (max 0 (T-δ)) T
    have hI : I ∈ 𝓝[<] T := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds
        (show max 0 (T-δ) < T from max_lt hT (by linarith))), self_mem_nhdsWithin] with t ht ht'
      exact ⟨ht,ht'⟩
    refine ⟨curve '' I, Filter.mem_map.mpr ?_, ?_⟩
    · exact mem_of_superset hI (fun t ht => mem_image_of_mem curve ht)
    · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
      have hu0 : u ∈ Ioo 0 T := ⟨(le_max_left _ _).trans_lt hu.1,hu.2⟩
      have hv0 : v ∈ Ioo 0 T := ⟨(le_max_left _ _).trans_lt hv.1,hv.2⟩
      have huv : |u-v| ≤ δ := by
        apply abs_le.mpr
        constructor <;> linarith [le_max_right (0:ℝ) (T-δ),hu.1,hu.2,hv.1,hv.2]
      have hid : δ*(M+1) = ε := by dsimp [δ]; field_simp
      calc _ ≤ M*|u-v| := hlip u v hu0 hv0
        _ ≤ M*δ := mul_le_mul_of_nonneg_left huv hM
        _ < ε := by nlinarith
  obtain ⟨y,hy⟩ := cauchy_map_iff_exists_tendsto.mp hcf
  refine ⟨y,hs.isClosed.mem_of_tendsto hy ?_,hy⟩
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hT), self_mem_nhdsWithin] with t ht ht'
  exact hmem t ⟨ht,ht'⟩

theorem compact_continuation (mass : ℝ) (a : Cartesian.Space) {s : Set Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1)
    (curve : ℝ → Phase) (T : ℝ) (hT : 0 < T)
    (hsol : ∀ t ∈ Ioo 0 T, HasDerivAt curve (phaseRhs mass a (curve t)) t)
    (hmem : ∀ t ∈ Ioo 0 T, curve t ∈ s) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ extended : ℝ → Phase, EqOn extended curve (Ioo 0 T) ∧
      (∀ t ∈ Ioo 0 (T+ε), HasDerivAt extended (phaseRhs mass a (extended t)) t) ∧
      ∀ t ∈ Ioo 0 (T+ε), 0 < Cartesian.radius a (extended t).1 := by
  obtain ⟨y,hy,hlim⟩ := compact_endpoint mass a hs hr curve T hT hsol hmem
  obtain ⟨next,hnext,ε,hε,hnsol⟩ := local_phase_solution mass a y T (hr y hy)
  have hrad : 0 < Cartesian.radius a (next T).1 := by rw [hnext]; exact hr y hy
  have hcr : ContinuousAt (fun t => Cartesian.radius a (next t).1) T :=
    ContinuousAt.comp (f := fun t => (next t).1) (g := Cartesian.radius a)
      (Cartesian.radius_smooth a (next T).1 hrad).continuousAt
      ((hnsol T ⟨by linarith,by linarith⟩).continuousAt.fst)
  obtain ⟨η,hη,hηbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcr.eventually (eventually_gt_nhds hrad))
  let ε0 := min ε (η/2)
  let extended : ℝ → Phase := fun t => if t < T then curve t else next t
  have heqleft : extended =ᶠ[𝓝[<] T] curve := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [extended,ite_eq_left (show t < T from ht)]
  have hextT : extended T = y := by simp [extended,hnext]
  have hinterval : Ioo (0:ℝ) T ∈ 𝓝[<] T := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hT),self_mem_nhdsWithin] with t ht ht'
    exact ⟨ht,ht'⟩
  have hdleft (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt extended (phaseRhs mass a (curve t)) t := by
    apply (hsol t ht).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht.2] with u hu
    simp only [extended,ite_eq_left (show u < T from hu)]
  have hcont : ContinuousWithinAt extended (Ioo 0 T) T := by
    rw [ContinuousWithinAt,hextT]
    exact ((tendsto_congr' heqleft).mpr hlim).mono_left (nhdsWithin_mono _ (fun t ht => ht.2))
  have hdlim : Tendsto (fun t => deriv extended t) (𝓝[<] T) (𝓝 (phaseRhs mass a y)) := by
    have heq : (fun t => deriv extended t) =ᶠ[𝓝[<] T] (fun t => phaseRhs mass a (curve t)) := by
      filter_upwards [hinterval] with t ht
      exact (hdleft t ht).deriv
    exact (tendsto_congr' heq).mpr ((phase_rhs_smooth mass a y (hr y hy)).continuousAt.tendsto.comp hlim)
  have hleft : HasDerivWithinAt extended (phaseRhs mass a y) (Iic T) T :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hdleft t ht).differentiableAt.differentiableWithinAt) hcont hinterval hdlim
  have hright : HasDerivWithinAt extended (phaseRhs mass a y) (Ici T) T := by
    have hd := (hnsol T ⟨by linarith,by linarith⟩).hasDerivWithinAt (s := Ici T)
    rw [hnext] at hd
    apply hd.congr_of_mem _ le_rfl
    intro t ht
    simp only [extended,ite_eq_right (not_lt.mpr ht)]
  have hend : HasDerivAt extended (phaseRhs mass a y) T := by
    have hd := hleft.union hright
    rwa [Iic_union_Ici,hasDerivWithinAt_univ] at hd
  refine ⟨ε0,by positivity,extended,fun t ht => by simp [extended,ht.2],?_,?_
    ⟩
  · intro t ht
    rcases lt_trichotomy t T with hlt|rfl|hgt
    · simpa only [show extended t = curve t from by simp [extended,hlt]] using hdleft t ⟨ht.1,hlt⟩
    · simpa only [hextT] using hend
    · have htupper : t < T+ε := ht.2.trans_le (add_le_add le_rfl (min_le_left _ _))
      have hd := hnsol t ⟨by linarith,htupper⟩
      have heq : extended =ᶠ[𝓝 t] next := by
        filter_upwards [Ioi_mem_nhds hgt] with u hu
        simp only [extended,ite_eq_right (not_lt.mpr hu.le)]
      have hd' := hd.congr_of_eventuallyEq heq
      simpa only [show extended t = next t from by simp [extended,not_lt.mpr hgt.le]] using hd'
  · intro t ht
    by_cases hlt : t < T
    · simpa only [extended,ite_eq_left hlt] using hr (curve t) (hmem t ⟨ht.1,hlt⟩)
    · have hd : dist t T < η := by
        rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (not_lt.mp hlt))]
        have hb : ε0 ≤ η/2 := min_le_right _ _
        linarith [ht.2]
      simpa only [extended,ite_eq_right hlt] using hηbound t hd

end BlackHole.KerrField
