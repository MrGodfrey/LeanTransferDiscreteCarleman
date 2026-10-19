module

public import Carleman.Spatial.CartesianSummationByParts
public import Carleman.Geometry.FiniteCartesianInteriorSum
public import Carleman.Spatial.CartesianKuhnEdgeAssembly

/-! The original standard (2d+1)-point Laplacian, its physical nodal pairing,
and the exact stiffness identity with the original weak Dirichlet form. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianPhysicalInner (δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f g : CartesianInteriorIndex N → ℝ) : ℝ := (∏ j, δ j)*∑ a, f a*g a

def cartesianFiniteDifferenceLaplacian (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f : CartesianInteriorIndex N → ℝ) (a : CartesianInteriorIndex N) : ℝ :=
  ∑ r, (2*f a-
    cartesianLatticeData o δ N f (cartesianLatticeSuccessor (cartesianInteriorLatticeIndex N a) r)-
    cartesianLatticeData o δ N f (cartesianLatticePredecessor (cartesianInteriorLatticeIndex N a) r))/(δ r)^2

theorem cartesianLatticeData_at_interior (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (a : CartesianInteriorIndex N) :
    cartesianLatticeData o δ N f (cartesianInteriorLatticeIndex N a)=f a :=
  cartesianInteriorData_at_node o δ hδ N f a

theorem cartesianAxisDifference_sum_by_parts (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) (r : Fin d) :
    (∑ z : ∀ j, Fin (N j), cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
      cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r)=
    ∑ z : ∀ j, Fin (N j),
      ((2*cartesianLatticeData o δ N f (fun j => ((z j).val:ℤ))-
        cartesianLatticeData o δ N f (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r)-
        cartesianLatticeData o δ N f (cartesianLatticePredecessor (fun j => ((z j).val:ℤ)) r))/(δ r)^2)*
      cartesianLatticeData o δ N g (fun j => ((z j).val:ℤ)) := by
  simp only [cartesianAxisDifference,div_mul_div_comm,← pow_two]
  simp only [div_mul_eq_mul_div,← Finset.sum_div]
  rw [cartesian_sum_axis_by_parts N r (cartesianLatticeData o δ N f) (cartesianLatticeData o δ N g)
    (fun z hz => cartesianLatticeData_zero_face o δ hδ N g z r hz)]

theorem cartesianFiniteDifferenceLaplacian_pairing_edges (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N f) g=
      (∏ j, δ j)*∑ z : ∀ j, Fin (N j), ∑ r : Fin d,
        cartesianAxisDifference o δ N f (fun j => ((z j).val:ℤ)) r*
        cartesianAxisDifference o δ N g (fun j => ((z j).val:ℤ)) r := by
  classical
  unfold cartesianPhysicalInner
  congr 1
  symm
  rw [Finset.sum_comm]
  simp_rw [cartesianAxisDifference_sum_by_parts o δ hδ N f g]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  let F : (Fin d → ℤ) → ℝ := fun z =>
    (∑ r, (2*cartesianLatticeData o δ N f z-
      cartesianLatticeData o δ N f (cartesianLatticeSuccessor z r)-
      cartesianLatticeData o δ N f (cartesianLatticePredecessor z r))/(δ r)^2)*
    cartesianLatticeData o δ N g z
  have hF : ∀ z : ∀ j, Fin (N j), (∃ j, (z j).val=0) → F (fun j => ((z j).val:ℤ))=0 := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    dsimp only [F]
    rw [cartesianLatticeData_zero_face o δ hδ N g _ j (Or.inl (by simp only [hj,Nat.cast_zero])),mul_zero]
  change (∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)))=_
  rw [cartesian_sum_zero_faces_to_interior N F hF]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [F,cartesianFiniteDifferenceLaplacian]
  rw [cartesianLatticeData_at_interior o δ hδ N f,cartesianLatticeData_at_interior o δ hδ N g]

theorem cartesianFiniteDifferenceLaplacian_weak_stiffness (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N f) g=
      weakGradientPairing (cartesianKuhnReconstructionJet o δ hδ N f)
        (cartesianKuhnReconstructionJet o δ hδ N g) := by
  rw [cartesianFiniteDifferenceLaplacian_pairing_edges o δ hδ N f g,
    cartesianKuhnReconstruction_weakGradientPairing_edges]

theorem cartesianFiniteDifferenceLaplacian_stiffness (hd : 0 < d)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f g : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N f) g=
      (boundedDirichletOriginalForm (openCoordinateBox_isOpen _ _) hd
        (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j))).scalarForm
        ⟨cartesianKuhnReconstructionLp o δ hδ N f,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f⟩
        ⟨cartesianKuhnReconstructionLp o δ hδ N g,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N g⟩ := by
  rw [cartesianFiniteDifferenceLaplacian_pairing_edges o δ hδ N f g,
    cartesianKuhnReconstruction_scalarForm_edges]

end Carleman
