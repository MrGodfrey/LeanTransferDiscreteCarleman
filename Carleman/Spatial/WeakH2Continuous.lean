module

public import Carleman.Spatial.WeakH2LocalContinuous
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Every original weak H² state in dimensions at most three has a genuine
continuous representative on its open domain. This is an interior result;
continuity on the domain closure is a separate boundary obligation. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.exists_continuous_representative
    (hS : IsOpen S) (hd : d ≤ 3) (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    let U := fun n => zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f S ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      ∀ x ∈ S, Tendsto (fun n => U n x) atTop (𝓝 (f x)) := by
  intro U
  let f := fun x => limUnder atTop (fun n => U n x)
  have hlocal (x : SpatialCoordinates d) (hx : x ∈ S) :
      ∃ r : ℝ, 0 < r ∧ ∃ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closedBall x r) ∧ TendstoUniformlyOn U g atTop (closedBall x r) := by
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hS x hx
    let r := ε/2
    have hr : 0 < r := half_pos hε
    have hsub : closedBall x r ⊆ S := (closedBall_subset_ball (half_lt_self hε)).trans hball
    have hvol : 0 < volume.real (closedBall x r) := ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior volume
        ⟨x,mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x hr)⟩).ne'
      (isCompact_closedBall x r).measure_ne_top
    have hdiam : ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r, dist y z ≤ 2*r := by
      intro y hy z hz
      have ht := dist_triangle y x z
      have h₁ : dist y x ≤ r := hy
      have h₂ : dist x z ≤ r := by simpa only [mem_closedBall,dist_comm] using hz
      linarith
    obtain ⟨g,hg,_,hu⟩ := WeakSobolevJet.exists_local_continuous_representative hS
      (isCompact_closedBall x r) (convex_closedBall x r) hsub hvol hd u (by positivity : 0 ≤ 2*r) hdiam
    exact ⟨r,hr,g,hg,hu⟩
  have hcont (x : SpatialCoordinates d) (hx : x ∈ S) : ContinuousAt f x := by
    obtain ⟨r,hr,g,hg,hu⟩ := hlocal x hx
    apply (hg.continuousAt (closedBall_mem_nhds x hr)).congr_of_eventuallyEq
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact (hu.tendsto_at hy).limUnder_eq
  have hlim (x : SpatialCoordinates d) (hx : x ∈ S) : Tendsto (fun n => U n x) atTop (𝓝 (f x)) := by
    obtain ⟨r,hr,g,_,hu⟩ := hlocal x hx
    have ht := hu.tendsto_at (mem_closedBall_self hr.le)
    change Tendsto (fun n => U n x) atTop (𝓝 (limUnder atTop (fun n => U n x)))
    rw [ht.limUnder_eq]
    exact ht
  refine ⟨f,fun x hx => (hcont x hx).continuousWithinAt,?_,hlim⟩
  filter_upwards [ae_restrict_mem hS.measurableSet,
    (spatialMollifier_converges (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))).filter_mono
      (ae_mono Measure.restrict_le_self),zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.value u)] with x hx hl he
  exact (tendsto_nhds_unique (hlim x hx) hl).trans he

theorem WeakSobolevJet.continuous_representative_unique
    (hS : IsOpen S) (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {f g : SpatialCoordinates d → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u)
    (hgu : g =ᵐ[volume.restrict S] WeakSobolevJet.value u) : EqOn f g S :=
  Measure.eqOn_open_of_ae_eq (hfu.trans hgu.symm) hS hf hg

end Carleman
