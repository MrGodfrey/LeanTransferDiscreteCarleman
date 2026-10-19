module

public import Carleman.Spatial.PhysicalFiniteLp
public import Carleman.Spatial.AllowedWeight

/-! Actual nodal multipliers and weights under the physical counting-L² isometry. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def BoundedMultiplier.ofFinite (b : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i, |b i| ≤ M) :
    BoundedMultiplier (Measure.count : Measure ι) where
  value := b
  measurable := (measurable_of_countable b).aestronglyMeasurable
  bound := M
  bound_nonneg := hM
  bounded := Filter.Eventually.of_forall hb

def SpatialProfile.ofFinite (r : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hr : ∀ i, |r i| ≤ R) :
    SpatialProfile (Measure.count : Measure ι) where
  value := r
  measurable := (measurable_of_countable r).aestronglyMeasurable
  bound := R
  bound_nonneg := hR
  bounded := Filter.Eventually.of_forall hr

namespace PhysicalFiniteSpace
variable {mass : ℝ} {hmass : 0 < mass}

theorem countLpEquiv_multiplier (b : BoundedMultiplier (Measure.count : Measure ι))
    (f : PhysicalFiniteSpace ι mass hmass) :
    countLpEquiv (multiplier b.value f) = b.map (countLpEquiv f) := by
  apply Lp.ext
  filter_upwards [b.map_ae (countLpEquiv f)] with i hi
  rw [hi,countLpEquiv_apply,countLpEquiv_apply,multiplier_apply]
  change Real.sqrt mass*(b.value i*f i)=b.value i*(Real.sqrt mass*f i)
  ring

theorem countLpEquiv_weighted_norm (b : BoundedMultiplier (Measure.count : Measure ι))
    (f : PhysicalFiniteSpace ι mass hmass) :
    b.seminorm (countLpEquiv f) = ‖multiplier b.value f‖ := by
  change ‖b.map (countLpEquiv f)‖ = _
  rw [← countLpEquiv_multiplier,countLpEquiv.norm_map]

theorem countLpEquiv_symm_map (b : BoundedMultiplier (Measure.count : Measure ι))
    (f : PhysicalFiniteSpace ι mass hmass) :
    countLpEquiv.symm (b.map (countLpEquiv f)) = multiplier b.value f := by
  rw [← countLpEquiv_multiplier,countLpEquiv.symm_apply_apply]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem multiplier_symmetric (b : ι → ℝ) : (multiplier (hmass := hmass) b).IsSymmetric := by
  intro f g
  rw [inner_eq,inner_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (b i*f i)*g i=f i*(b i*g i)
  ring

theorem multiplier_opNorm_le (b : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i, |b i| ≤ M) :
    ‖multiplier (hmass := hmass) b‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  let B := BoundedMultiplier.ofFinite b M hM hb
  have he := countLpEquiv_weighted_norm B f
  have hh := B.seminorm_le (countLpEquiv f)
  rw [he,countLpEquiv.norm_map] at hh
  exact hh

end PhysicalFiniteSpace
end Carleman
