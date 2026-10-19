module

public import Carleman.Geometry.KuhnFaceMatching
public import Carleman.Spatial.SimplexCoordinateBoundary
public import Carleman.Spatial.NodalDirichletMembership
public import Carleman.Geometry.CoordinateBoxConvexity

/-! Genuine globally continuous nodal hats on the concrete finite Kuhn grid.
Interior-node hats have zero extension in the original H¹₀ graph closure. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnPartition_boundaryFitted (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) : (cartesianKuhnPartition o δ hδ N).BoundaryFitted := by
  intro i x hx
  apply simplex_mem_convexHull_positive_support _ hx.1
  intro k hk
  refine ⟨mem_range_self k,?_⟩
  apply simplex_coordinateBox_boundary_support o _ ?_
    (cartesianFiniteSimplex o δ hδ N i) ((cartesianKuhnPartition o δ hδ N).inside i) hx.1 hx.2 k hk
  intro j
  have hi := (i.1 j).isLt
  have hn : 0 < N j := by omega
  have hnr : 0 < (N j:ℝ) := by exact_mod_cast hn
  linarith [mul_pos hnr (hδ j)]

def cartesianKuhnHat (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) : SpatialCoordinates d → ℝ :=
  (cartesianKuhnPartition o δ hδ N).nodalFunction
    (fun x => if x=cartesianGridPoint o δ a then 1 else 0)

theorem cartesianKuhnHat_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnHat o δ hδ N a x = ∑ k,
      if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianGridPoint o δ a
      then simplexBarycentric (cartesianFiniteSimplex o δ hδ N i) k x else 0 := by
  rw [cartesianKuhnHat,(cartesianKuhnPartition o δ hδ N).nodalFunction_on_cell
    (cartesianKuhnPartition_faceMatching o δ hδ N) _ i hx,
    SimplicialPartition.localNodal,simplexNodalInterpolant_apply]
  simp only [ite_mul,one_mul,zero_mul]
  rfl

theorem cartesianKuhnHat_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N) (k : Fin (d+1)) :
    cartesianKuhnHat o δ hδ N a ((cartesianFiniteSimplex o δ hδ N i).points k)=
      if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianGridPoint o δ a then 1 else 0 :=
  (cartesianKuhnPartition o δ hδ N).nodalFunction_vertex
    (cartesianKuhnPartition_faceMatching o δ hδ N) _ i k

theorem cartesianKuhnHat_data_boundary (o δ : Fin d → ℝ) (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    {x : SpatialCoordinates d} (hx : x ∈ frontier (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :
    (if x=cartesianGridPoint o δ a then (1:ℝ) else 0)=0 := by
  apply ite_eq_right
  intro he
  subst x
  exact hx.2 ((openCoordinateBox_isOpen _ _).interior_eq.symm ▸ ha)

theorem cartesianKuhnHat_continuous (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    Continuous (cartesianKuhnHat o δ hδ N a) :=
  (cartesianKuhnPartition o δ hδ N).nodalFunction_continuous_of_boundary
    (openCoordinateBox_isOpen _ _) (cartesianKuhnPartition_faceMatching o δ hδ N)
    (cartesianKuhnPartition_boundaryFitted o δ hδ N) _
    (fun _ _ hx => cartesianKuhnHat_data_boundary o δ N a ha hx)

theorem cartesianKuhnHat_zero_compl (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    {x : SpatialCoordinates d} (hx : x ∉ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    cartesianKuhnHat o δ hδ N a x=0 :=
  (cartesianKuhnPartition o δ hδ N).nodalFunction_zero_on_compl
    (openCoordinateBox_isOpen _ _) (cartesianKuhnPartition_faceMatching o δ hδ N)
    (cartesianKuhnPartition_boundaryFitted o δ hδ N) _
    (fun _ _ hy => cartesianKuhnHat_data_boundary o δ N a ha hy) hx

theorem cartesianKuhnHat_compact (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) : HasCompactSupport (cartesianKuhnHat o δ hδ N a) :=
  (cartesianKuhnPartition o δ hδ N).nodalFunction_hasCompactSupport _

theorem cartesianKuhnHat_nonneg (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (x : SpatialCoordinates d) :
    0 ≤ cartesianKuhnHat o δ hδ N a x := by
  by_cases hx : x ∈ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  · rw [← (cartesianKuhnPartition o δ hδ N).cells_union] at hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [cartesianKuhnHat_on_cell o δ hδ N a i hi]
    exact Finset.sum_nonneg fun k _ => ite_nonneg (simplexBarycentric_nonneg _ hi k) (le_refl 0)
  · have he := (cartesianKuhnPartition o δ hδ N).nodalFunction_zero_outside
      (fun y => if y=cartesianGridPoint o δ a then (1:ℝ) else 0) hx
    change cartesianKuhnHat o δ hδ N a x=0 at he
    exact he.ge

theorem cartesianKuhnHat_le_one (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (x : SpatialCoordinates d) :
    cartesianKuhnHat o δ hδ N a x ≤ 1 := by
  by_cases hx : x ∈ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  · have h := (cartesianKuhnPartition o δ hδ N).nodalFunction_abs_le
      (cartesianKuhnPartition_faceMatching o δ hδ N)
      (fun y => if y=cartesianGridPoint o δ a then (1:ℝ) else 0) 1
      (fun i k => by split_ifs <;> norm_num) hx
    exact (le_abs_self _).trans h
  · have he := (cartesianKuhnPartition o δ hδ N).nodalFunction_zero_outside
      (fun y => if y=cartesianGridPoint o δ a then (1:ℝ) else 0) hx
    change cartesianKuhnHat o δ hδ N a x=0 at he
    rw [he]
    norm_num

def cartesianKuhnHatLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  (cartesianKuhnPartition o δ hδ N).nodalLp (openCoordinateBox_isOpen _ _).measurableSet
    (cartesianKuhnPartition_faceMatching o δ hδ N)
    (fun x => if x=cartesianGridPoint o δ a then 1 else 0)

theorem cartesianKuhnHatLp_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) :
    cartesianKuhnHatLp o δ hδ N a =ᵐ[volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))]
      cartesianKuhnHat o δ hδ N a :=
  (cartesianKuhnPartition o δ hδ N).nodalLp_ae (openCoordinateBox_isOpen _ _).measurableSet
    (cartesianKuhnPartition_faceMatching o δ hδ N) _

theorem cartesianKuhnHatLp_mem_dirichlet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    cartesianKuhnHatLp o δ hδ N a ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
  (cartesianKuhnPartition o δ hδ N).nodalLp_mem_dirichletSubspace
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
    (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianKuhnPartition_boundaryFitted o δ hδ N) _
    (fun _ _ hx => cartesianKuhnHat_data_boundary o δ N a ha hx)

end Carleman
