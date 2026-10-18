module

public import Carleman.Spatial.FullConformingNodal
public import Carleman.Spatial.UniformNodalProjection

/-! The original weighted L² projection estimate on the full H¹₀ piecewise
affine space. Nodal representation and boundary values are supplied internally. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem allowed_weight_full_projection
    {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (γ : ℝ) (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (ℓ : ι → ℝ), (∀ i, 0 < ℓ i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 → ∀ (inverseSize : Bool),
    ∀ (u : Lp ℝ 2 (volume.restrict S)),
    (M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).seminorm
      ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
        Lp ℝ 2 (volume.restrict S)) ≤
      C*(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).seminorm u := by
  obtain ⟨δ,hδ,hd,C,hC,hbound⟩ :=
    allowed_weight_projection_of_nodal_representation hS hc hcompact ρ hρ γ hγ hΓ
  refine ⟨δ,hδ,hd,C,hC,?_⟩
  intro ι _ M hM hB ℓ hℓ hg w hm τ t η hη inverseSize u
  obtain ⟨f,hf,hproj⟩ := M.conforming_dirichlet_nodal_representation hS hc hM
    ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u)
    ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u).property
  exact hbound ι M hM hB ℓ hℓ hg w hm τ t η hη inverseSize u f hf hproj

end Carleman
