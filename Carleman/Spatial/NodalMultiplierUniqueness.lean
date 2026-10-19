module

public import Carleman.Spatial.SimplicialNodalOperator
public import Carleman.Spatial.SimplicialIntegrals
public import Carleman.Spatial.CartesianKuhnReconstructionJet

/-! Equality of actual nodal L² classes forces equality of their vertex data.
Thus multiplying the nodal data does not depend on a chosen representation.
No arbitrary L² class is evaluated at a vertex. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}

namespace SimplicialPartition
variable (M : SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodalLp_vertex_eq (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching)
    (f g : SpatialCoordinates d → ℝ)
    (he : M.nodalLp hS.measurableSet hM f=M.nodalLp hS.measurableSet hM g)
    (i : ι) (k : Fin (d+1)) : f ((M.simplex i).points k)=g ((M.simplex i).points k) := by
  have hf := (M.nodalLp_ae hS.measurableSet hM f).filter_mono (ae_mono (M.cell_measure_le_domain hS hc i))
  have hg := (M.nodalLp_ae hS.measurableSet hM g).filter_mono (ae_mono (M.cell_measure_le_domain hS hc i))
  rw [he] at hf
  have ha : M.localNodal f i =ᵐ[volume.restrict (M.cell i)] M.localNodal g i := by
    filter_upwards [hf,hg,ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hy hz
    have ht := hx.symm.trans hy
    rwa [M.nodalFunction_on_cell hM f i hz,M.nodalFunction_on_cell hM g i hz] at ht
  have hpoint := Measure.eqOn_of_ae_eq ha
    (M.localNodal f i).continuous_of_finiteDimensional.continuousOn
    (M.localNodal g i).continuous_of_finiteDimensional.continuousOn
    (simplexCell_subset_closure_interior (M.simplex i))
  simpa only [M.localNodal_vertex] using
    hpoint (subset_convexHull ℝ _ (Set.mem_range_self k))

theorem nodalLp_multiplier_congr (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching)
    (ω f g : SpatialCoordinates d → ℝ)
    (he : M.nodalLp hS.measurableSet hM f=M.nodalLp hS.measurableSet hM g) :
    M.nodalLp hS.measurableSet hM (fun x => ω x*f x)=
      M.nodalLp hS.measurableSet hM (fun x => ω x*g x) := by
  apply M.nodalLp_congr
  intro i k
  rw [M.nodalLp_vertex_eq hS hc hM f g he i k]

end SimplicialPartition

theorem cartesianKuhnReconstructionLp_mem_conforming (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N f ∈
      (cartesianKuhnPartition o δ hδ N).conformingSpace
        (dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) := by
  rw [cartesianKuhnReconstructionLp_eq_nodal]
  apply (cartesianKuhnPartition o δ hδ N).nodalLp_mem_dirichletConformingSpace
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
    (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianKuhnPartition_boundaryFitted o δ hδ N)
  intro i k hk
  apply cartesianInteriorData_zero_compl o δ hδ N f
  exact fun hi => hk.2 ((openCoordinateBox_isOpen _ _).interior_eq.symm ▸ hi)

end Carleman
