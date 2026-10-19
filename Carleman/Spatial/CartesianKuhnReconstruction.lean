module

public import Carleman.Spatial.CartesianKuhnLoadLift

/-! The original reconstruction is the finite sum of actual interior-node
hats, with the exact local nodal interpolation formula. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnReconstruction (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ a, f a*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x

theorem cartesianKuhnReconstruction_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnReconstruction o δ hδ N f x=
      simplexNodalInterpolant (cartesianFiniteSimplex o δ hδ N i)
        (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k)) x := by
  classical
  simp only [cartesianKuhnReconstruction,cartesianKuhnHat_on_cell o δ hδ N _ i hx,
    simplexNodalInterpolant_apply,cartesianInteriorData]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_ite,ite_mul,mul_zero,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  simp only [cartesianInteriorPoint,eq_comm]
  rfl

theorem cartesianKuhnReconstruction_continuous (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    Continuous (cartesianKuhnReconstruction o δ hδ N f) := by
  apply continuous_finsetSum
  intro a _
  exact continuous_const.mul (cartesianKuhnHat_continuous o δ hδ N _ (cartesianInteriorPoint_mem o δ hδ N a))

theorem cartesianKuhnReconstruction_compact (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    HasCompactSupport (cartesianKuhnReconstruction o δ hδ N f) := by
  have h : HasCompactSupport (∑ a : CartesianInteriorIndex N,
      (fun x => f a*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x)) := by
    apply HasCompactSupport.finset_sum
    intro a _
    exact (cartesianKuhnHat_compact o δ hδ N _).mul_left
  convert h using 1
  funext x
  simp only [cartesianKuhnReconstruction,Finset.sum_apply]

theorem cartesianKuhnReconstruction_memLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    MemLp (cartesianKuhnReconstruction o δ hδ N f) 2 volume :=
  (cartesianKuhnReconstruction_continuous o δ hδ N f).memLp_of_hasCompactSupport
    (cartesianKuhnReconstruction_compact o δ hδ N f)

theorem cartesianKuhnReconstruction_sq_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    Integrable (fun x => (cartesianKuhnReconstruction o δ hδ N f x)^2) volume := by
  convert (cartesianKuhnReconstruction_memLp o δ hδ N f).integrable_mul
    (cartesianKuhnReconstruction_memLp o δ hδ N f) using 1
  funext x
  exact sq _

end Carleman
