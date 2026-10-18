module

public import Carleman.Spatial.HeatNormSquare
public import Carleman.Spatial.WeightedEnergySeminorm
public import Carleman.Spatial.FullWeightedProjection

/-! Projection error algebra in the actual L² space and the genuine weak H¹
norm. The residual need not be assigned unproved boundary regularity. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem WeakSobolevJet.heat_weightedNorm_le_fields
    {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} {q : ℝ} (hq : 0 ≤ q) (σ : BoundedMultiplier ν)
    (u : WeakSobolevJet d 1 ν S) :
    weightedNorm q σ u ≤ q*σ.seminorm (value u)+σ.seminorm (field 1 u) := by
  apply (sq_le_sq₀ (weightedNorm_nonneg _ _ _) (by positivity [apply_nonneg σ.seminorm (value u),apply_nonneg σ.seminorm (field 1 u)])).mp
  rw [heat_weightedNorm_sq]
  nlinarith [mul_nonneg (mul_nonneg hq (apply_nonneg σ.seminorm (value u))) (apply_nonneg σ.seminorm (field 1 u))]

theorem projection_error_of_residual {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (v I e : Lp ℝ 2 ν)
    (hI : I ∈ X) (he : e=v-I) :
    (X.orthogonalProjectionOnto v : Lp ℝ 2 ν)-v =
      (X.orthogonalProjectionOnto e : Lp ℝ 2 ν)-e := by
  rw [he,map_sub]
  have hfix : X.orthogonalProjectionOnto I = (⟨I,hI⟩ : X) :=
    X.orthogonalProjectionOnto_mem_subspace_eq_self ⟨I,hI⟩
  rw [hfix,Submodule.coe_sub]
  abel

theorem weak_projected_residual_estimate
    {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} {q CI Cp : ℝ} (hq : 0 ≤ q) (hCI : 0 ≤ CI)
    (ξ ζ : BoundedMultiplier ν) (p e : WeakSobolevJet d 1 ν S)
    (hzero : ξ.seminorm (WeakSobolevJet.value p) ≤ Cp*ξ.seminorm (WeakSobolevJet.value e))
    (hmesh : ζ.seminorm (WeakSobolevJet.value p) ≤ Cp*ζ.seminorm (WeakSobolevJet.value e))
    (hinv : ξ.seminorm (WeakSobolevJet.field 1 p) ≤ CI*ζ.seminorm (WeakSobolevJet.value p)) :
    WeakSobolevJet.weightedNorm q ξ (p-e) ≤
      ξ.seminorm (WeakSobolevJet.field 1 e)+CI*Cp*ζ.seminorm (WeakSobolevJet.value e)+
        (1+Cp)*(q*ξ.seminorm (WeakSobolevJet.value e)) := by
  apply (WeakSobolevJet.weightedNorm_sub_le hq ξ p e).trans
  have hp := WeakSobolevJet.heat_weightedNorm_le_fields hq ξ p
  have he := WeakSobolevJet.heat_weightedNorm_le_fields hq ξ e
  have hz := mul_le_mul_of_nonneg_left hzero hq
  have hi := hinv.trans (mul_le_mul_of_nonneg_left hmesh hCI)
  nlinarith only [hp,he,hz,hi]

end Carleman
