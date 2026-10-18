module

public import Carleman.Spatial.SimplicialLocalGradient

/-! Every actual conforming piecewise affine H¹ state, without any nodal
ansatz, has the same local polynomial and genuine weak gradient. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def affinePolynomialOfCoefficients (c : Fin (d+1) → ℝ) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (SpatialCoordinates d) (c 0) +
    (∑ j : Fin d, c j.succ • (EuclideanSpace.proj j).toLinearMap).toAffineMap

theorem affinePolynomialOfCoefficients_apply (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    affinePolynomialOfCoefficients c x = c 0+∑ j : Fin d, c j.succ*x j := by
  simp [affinePolynomialOfCoefficients]

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem conforming_local_polynomial (hS : IsOpen S) (hc : Convex ℝ S)
    (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ M.conformingSpace V) (i : ι) :
    ∃ p : SpatialCoordinates d →ᵃ[ℝ] ℝ,
      (WeakSobolevJet.value u =ᵐ[volume.restrict (M.cell i)] p) ∧
      (WeakSobolevJet.field 1 u =ᵐ[volume.restrict (M.cell i)]
        (fun x => derivativeOneFiber (fderiv ℝ p x))) := by
  obtain ⟨c,hc⟩ := ((M.mem_conformingSpace_iff hS.measurableSet V _).mp hu).2 i
  let p := affinePolynomialOfCoefficients c
  have hp : ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → WeakSobolevJet.value u x=p x := by
    filter_upwards [hc] with x hx
    intro hi
    exact (hx hi).trans (affinePolynomialOfCoefficients_apply c x).symm
  refine ⟨p,?_,M.gradient_on_cell hS ‹Convex ℝ S› u i p hp⟩
  filter_upwards [hp.filter_mono (ae_mono (M.cell_measure_le_domain hS ‹Convex ℝ S› i)),
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hi
  exact hx hi

end SimplicialPartition
end Carleman
