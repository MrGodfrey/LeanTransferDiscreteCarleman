module

public import Carleman.Spatial.MollifiedGradientEnergy
public import Carleman.Spatial.PairwiseL2Limit
public import Carleman.Spatial.FullSpaceInterpolation
public import Mathlib.Topology.MetricSpace.Thickening

/-! Mean Poincaré for genuine weak derivatives on compact convex subsets
strictly inside the original open domain. The derivative bound is the
original L² energy; no global weak derivative of a zero extension is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped Convolution Topology
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem shrinkingBump_rOut_tendsto :
    Tendsto (fun n => (shrinkingBump d n).rOut) atTop (𝓝 (0:ℝ)) := by
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 using 1 <;>
    simp [shrinkingBump,div_eq_mul_inv]

theorem compact_mollifier_eventually_inside (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ tsupport (spatialMollifier d n).value, x-y ∈ S := by
  obtain ⟨δ,hδ,hbuffer⟩ := hK.exists_cthickening_subset_open hS hKS
  filter_upwards [shrinkingBump_rOut_tendsto.eventually (gt_mem_nhds hδ)] with n hn
  intro x hx y hy
  apply hbuffer
  apply mem_cthickening_of_dist_le (x-y) x δ K hx
  rw [dist_eq_norm,show x-y-x = -y by abel,norm_neg]
  have hh : y ∈ closedBall (0 : SpatialCoordinates d) (shrinkingBump d n).rOut := by
    rw [← (shrinkingBump d n).tsupport_normed_eq (μ := volume)]
    exact hy
  have hnorm : ‖y‖ ≤ (shrinkingBump d n).rOut := by
    simpa only [mem_closedBall,dist_zero_right] using hh
  exact hnorm.trans hn.le

theorem interior_weak_pairwise_fullLp (hS : IsOpen S) (hK : IsCompact K)
    (hc : Convex ℝ K) (hKS : K ⊆ S)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, ∫ y in K, (u x-u y)^2) ≤
      (2:ℝ)^d*volume.real K*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  let F := fun n => u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
  have hm (n : ℕ) : MemLp (F n) 2 (volume.restrict K) :=
    ((spatialMollifier d n).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) u).1.restrict K
  apply pairwise_square_bound_of_ae_tendsto ((Lp.memLp u).restrict K) hm
    ((spatialMollifier_converges u).filter_mono (ae_mono Measure.restrict_le_self)) (by positivity)
  filter_upwards [compact_mollifier_eventually_inside hS hK hKS] with n hn
  exact convex_mollified_pairwise_bound hK hc u v hv (spatialMollifier d n)
    (spatialMollifier_nonneg n) (spatialMollifier_integral n) hn hD hdiam

theorem interior_weak_pairwise (hS : IsOpen S) (hK : IsCompact K)
    (hc : Convex ℝ K) (hKS : K ⊆ S)
    (u : Lp ℝ 2 (volume.restrict S)) (v : Fin d → Lp ℝ 2 (volume.restrict S))
    (hv : ∀ i, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, ∫ y in K, (u x-u y)^2) ≤
      (2:ℝ)^d*volume.real K*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  have he := interior_weak_pairwise_fullLp hS hK hc hKS (zeroExtendLp hS.measurableSet u)
    (fun i => zeroExtendLp hS.measurableSet (v i))
    (fun i => (hv i).zeroExtend hS.measurableSet) hD hdiam
  simp only [zeroExtendLp_norm] at he
  have hae : zeroExtendLp hS.measurableSet u =ᵐ[volume.restrict K] u :=
    (zeroExtendLp_ae_restrict hS.measurableSet u).filter_mono
      (ae_mono (Measure.restrict_mono hKS le_rfl))
  rwa [pairwise_integral_congr_ae hae] at he

theorem interior_weak_mean_poincare (hS : IsOpen S) (hK : IsCompact K)
    (hc : Convex ℝ K) (hKS : K ⊆ S) (hvol : 0 < volume.real K)
    (u : Lp ℝ 2 (volume.restrict S)) (v : Fin d → Lp ℝ 2 (volume.restrict S))
    (hv : ∀ i, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    (∫ x in K, (u x-(∫ y in K, u y)/volume.real K)^2) ≤
      (2:ℝ)^d/2*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hae : zeroExtendLp hS.measurableSet u =ᵐ[volume.restrict K] u :=
    (zeroExtendLp_ae_restrict hS.measurableSet u).filter_mono
      (ae_mono (Measure.restrict_mono hKS le_rfl))
  have hm : MemLp u 2 (volume.restrict K) := (memLp_congr_ae hae).mp
    ((Lp.memLp (zeroExtendLp hS.measurableSet u)).restrict K)
  have he := mean_square_pairwise_identity hm (by simpa using hvol)
  simp only [measureReal_restrict_apply_univ] at he
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ) < 2) hvol)).mp
  rw [he]
  exact (interior_weak_pairwise hS hK hc hKS u v hv hD hdiam).trans_eq (by ring)

end Carleman
