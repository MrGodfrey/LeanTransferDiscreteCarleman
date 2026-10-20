module

public import Carleman.Control.P1TestInterpolation
public import Carleman.Control.CartesianDirichletReconstruction
public import Carleman.Geometry.CartesianKuhnShape
public import Carleman.Geometry.CartesianInteriorVertex

/-! Original nodal sampling and actual Kuhn reconstruction, with fixed-box mesh geometry. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def cartesianNodalSample (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) : CartesianPhysicalState δ hδ N :=
  PhysicalFiniteSpace.valuesEquiv.symm (fun a => f (cartesianInteriorPoint o δ N a))

theorem cartesianNodalSample_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (a : CartesianInteriorIndex N) :
    cartesianNodalSample o δ hδ N f a=f (cartesianInteriorPoint o δ N a) := rfl

theorem cartesianInteriorData_test_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (φ : SpatialTest (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
    (i : CartesianCellIndex N) (k : Fin (d+1)) :
    cartesianInteriorData o δ N (cartesianNodalSample o δ hδ N φ.value)
      ((cartesianFiniteSimplex o δ hδ N i).points k)=φ.value ((cartesianFiniteSimplex o δ hδ N i).points k) := by
  classical
  by_cases hx : (cartesianFiniteSimplex o δ hδ N i).points k ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)
  · obtain ⟨a,ha⟩ := cartesianFiniteSimplex_interior_vertex o δ hδ N i k hx
    rw [← ha,cartesianInteriorData_at_node o δ hδ N,cartesianNodalSample_apply]
  · rw [cartesianInteriorData_zero_compl o δ hδ N _ hx]
    symm
    exact image_eq_zero_of_notMem_tsupport (fun hs => hx (φ.support hs))

theorem cartesianKuhnReconstructionLp_test_eq_nodal (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (φ : SpatialTest (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :
    cartesianKuhnReconstructionLp o δ hδ N (cartesianNodalSample o δ hδ N φ.value)=
      (cartesianKuhnPartition o δ hδ N).nodalLp (openCoordinateBox_isOpen _ _).measurableSet
        (cartesianKuhnPartition_faceMatching o δ hδ N) φ.value := by
  rw [cartesianKuhnReconstructionLp_eq_nodal]
  exact (cartesianKuhnPartition o δ hδ N).nodalLp_congr _ _
    (cartesianInteriorData_test_vertex o δ hδ N φ)

def cartesianBoxKuhnPartition (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) :
    SimplicialPartition (openCoordinateBox lo hi) (CartesianCellIndex N) :=
  (funext hbox) ▸ cartesianKuhnPartition lo δ hδ N

theorem cartesianBoxKuhnPartition_faceMatching (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) :
    (cartesianBoxKuhnPartition lo hi δ hδ N hbox).FaceMatching := by
  have he := funext hbox
  subst hi
  exact cartesianKuhnPartition_faceMatching lo δ hδ N

theorem cartesianBoxKuhnPartition_boundaryFitted (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) :
    (cartesianBoxKuhnPartition lo hi δ hδ N hbox).BoundaryFitted := by
  have he := funext hbox
  subst hi
  exact cartesianKuhnPartition_boundaryFitted lo δ hδ N

theorem cartesianBoxDirichletState_test_eq_nodal (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (φ : SpatialTest (openCoordinateBox lo hi)) :
    cartesianBoxDirichletState lo hi δ hδ N hbox (cartesianNodalSample lo δ hδ N φ.value)=
      (cartesianBoxKuhnPartition lo hi δ hδ N hbox).testDirichletState
        (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
        (cartesianBoxKuhnPartition_faceMatching lo hi δ hδ N hbox)
        (cartesianBoxKuhnPartition_boundaryFitted lo hi δ hδ N hbox) φ := by
  apply conformingEmbed_injective (dirichletSubspace (openCoordinateBox lo hi))
    (openCoordinateBox_isOpen _ _) (ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet)
  change dirichletStateValue _ _=dirichletStateValue _ _
  rw [SimplicialPartition.testDirichletState_value,cartesianBoxDirichletState_value]
  have he := funext hbox
  subst hi
  change WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N _)=_
  rw [cartesianKuhnReconstructionJet_value]
  exact cartesianKuhnReconstructionLp_test_eq_nodal lo δ hδ N φ

theorem cartesianBoxKuhnPartition_maxDiameter_le (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h) :
    (cartesianBoxKuhnPartition lo hi δ hδ N hbox).maxDiameter ≤ (d+1:ℝ)*h := by
  have he := funext hbox
  subst hi
  exact cartesianKuhn_maxDiameter_le lo δ hδ N h hh hstep

theorem cartesianBoxKuhn_uniform_inballs (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∃ (a : CartesianCellIndex N → SpatialCoordinates d) (r : ℝ), 0 < r ∧
        (∀ i, Metric.ball (a i) r ⊆ (cartesianBoxKuhnPartition lo hi δ hδ N hbox).cell i) ∧
        (∀ i, (cartesianBoxKuhnPartition lo hi δ hδ N hbox).cellDiameter i ≤ C*r) := by
  obtain ⟨C,hC,h⟩ := cartesianKuhn_uniform_inballs (d := d) κ hκ
  refine ⟨C,hC,?_⟩
  intro lo hi δ hδ N hbox hh hhpos hl hu
  have he := funext hbox
  subst hi
  exact h lo δ hδ N hh hhpos hl hu

end Carleman
