module

public import Carleman.Spatial.WeightedTime

/-! The original elliptic regularity bound (A1) transfers measurability and
L² regularity of A u to the genuine weak Sobolev graph, not just to the
numerical values of derivative norms. Domain representatives are only a.e.
representatives of the original H-valued trajectory. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

def domainSobolevJet : D →ₗ[ℝ] WeakSobolevJet d n ν S :=
  (sobolevJetEquiv hS hν).symm.toLinearMap.comp (D.inclusion hD)

theorem domainSobolevJet_value (v : D) :
    WeakSobolevJet.value (domainSobolevJet hS hν hD v) = (v : Lp ℝ 2 ν) :=
  LinearEquiv.ofInjective_symm_apply _ (h := WeakSobolevJet.value_injective hS hν)
    (D.inclusion hD v)

/-- Elliptic regularity implies injectivity of A through the actual zeroth field. -/
theorem injective_of_elliptic_bound (A : D →ₗ[ℝ] Lp ℝ 2 ν) (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖) :
    Function.Injective A := by
  intro v z hvz
  have hn := hell (v-z)
  rw [map_sub, map_sub, hvz, sub_self, norm_zero, mul_zero] at hn
  have hj := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  apply Subtype.ext
  simpa only [domainSobolevJet_value] using congrArg WeakSobolevJet.value hj

/-- A1 supplies a bounded inverse into the Sobolev graph on range(A).
Measurability lifts to the subspace range without assuming it is all of H,
closed, or already associated with an existence theorem. -/
theorem memLp_domainSobolevJet_of_operator (A : D →ₗ[ℝ] Lp ℝ 2 ν) (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖)
    {μ : Measure ℝ} {u : ℝ → D} (hu : MemLp (fun t => A (u t)) 2 μ) :
    MemLp (fun t => domainSobolevJet hS hν hD (u t)) 2 μ := by
  let e := LinearEquiv.ofInjective A (injective_of_elliptic_bound hS hν hD A C hell)
  let J := domainSobolevJet hS hν hD
  let K : LinearMap.range A →L[ℝ] WeakSobolevJet d n ν S :=
    (J.comp e.symm.toLinearMap).mkContinuous C (by
      intro y
      change ‖J (e.symm y)‖ ≤ C * ‖(y : Lp ℝ 2 ν)‖
      have he : A (e.symm y) = (y : Lp ℝ 2 ν) :=
        LinearEquiv.ofInjective_symm_apply A y
      simpa only [he] using hell (e.symm y))
  have hr : AEStronglyMeasurable (fun t => A.rangeRestrict (u t)) μ :=
    (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp hu.aestronglyMeasurable
  have hk : ∀ t, K (A.rangeRestrict (u t)) = J (u t) := by
    intro t
    change J (e.symm (e (u t))) = _
    rw [e.symm_apply_apply]
  have hm := K.continuous.comp_aestronglyMeasurable hr
  simp_rw [hk] at hm
  exact hu.of_le_mul hm (Filter.Eventually.of_forall fun t => hell (u t))

namespace PeriodicWeakTrajectory
variable {g : TimeGrid} {A : D →ₗ[ℝ] Lp ℝ 2 ν}

/-- The existing B1 trajectory, with only a.e. domain membership, has a
genuine Bochner L² Sobolev representative under the original A1 estimate. -/
theorem domainSobolev_L2 (u : PeriodicWeakTrajectory g D A) (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖) :
    MemLp (fun t => domainSobolevJet hS hν hD (u.domainValue t)) 2 g.timeMeasure :=
  memLp_domainSobolevJet_of_operator hS hν hD A C hell u.operator_L2

/-- All weighted graph densities are now finite for a B1 trajectory using A1.
No extra time measurability of named derivative fields is assumed. -/
theorem weighted_domain_field_finite (u : PeriodicWeakTrajectory g D A) (C : ℝ)
    (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ C * ‖A v‖)
    (w : TimeWeight) (ρ : SpatialProfile ν) (τ s : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) (k : Fin (n+1)) :
    TimeSquareIntegrable g w.q s
      (fun t => (ρ.multiplier w τ t).seminorm.comp
        ((WeakSobolevJet.field k).comp (domainSobolevJet hS hν hD))) u.domainValue :=
  WeakSobolevJet.timeSquareIntegrable_field g w ρ τ s hq (u.domainSobolev_L2 hS hν hD C hell) k

end PeriodicWeakTrajectory
end Carleman
