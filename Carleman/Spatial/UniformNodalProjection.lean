module

public import Carleman.Spatial.NodalProjectionEstimate
public import Carleman.Spatial.AllowedReciprocalWeight

/-! Mesh-uniform projection stability for all four actual weights, conditional only
on the still-explicit nodal representation and zero boundary nodal data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem allowed_weight_projection_of_nodal_representation
    {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (γ : ℝ) (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
    ∀ (hM : M.FaceMatching), M.BoundaryFitted →
    ∀ (ℓ : ι → ℝ), (∀ i, 0 < ℓ i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 → ∀ (inverseSize : Bool),
    ∀ (u : Lp ℝ 2 (volume.restrict S)) (f : SpatialCoordinates d → ℝ),
      (∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) →
      ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
        Lp ℝ 2 (volume.restrict S)) = M.nodalLp hS.measurableSet hM f →
    (M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).seminorm
      ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
        Lp ℝ 2 (volume.restrict S)) ≤
      C*(M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)).seminorm u := by
  obtain ⟨δ,hδ,hd,hθ,hstrict,huniform⟩ :=
    allowed_weights_uniform_nodal_weights hS hc hcompact ρ hρ γ hγ hΓ
  let θ := (γ+p1GradingLimit d)/2
  have hθpos : 0 < θ := zero_lt_one.trans_le hθ
  refine ⟨δ,hδ,hd,θ^3*(d+2)/p1MassMargin d θ,
    div_pos (mul_pos (pow_pos hθpos _) (by positivity)) (p1MassMargin_pos hθ hstrict),?_⟩
  intro ι _ M hM hB ℓ hℓ hg w hm τ t η hη inverseSize u f hf hproj
  obtain ⟨_,hbounds,hcomp⟩ := huniform ι M ℓ hℓ hg w hm τ t η hη inverseSize
  let a := M.gradedCellWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t)
  have ha (i : ι) : 0 < a i := M.gradedCellWeight_pos inverseSize ℓ hℓ ρ w τ t η i
  have hag : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j := by
    intro i j hij
    obtain ⟨k,l,hkl⟩ := hij
    have hi := (hbounds i k).1
    rw [hkl] at hi
    have hh := hi.trans (hbounds j l).2
    simpa only [mul_comm θ] using (div_le_iff₀ hθpos).mp hh
  apply M.weighted_projection_bound_of_nodal_representation hS hc hM hB
    (M.gradedWeight inverseSize ℓ ((ρ.scaled η).multiplier w τ t))
    (M.gradedReciprocalWeight inverseSize ℓ ρ w τ t η)
    (M.gradedReciprocalWeight_product hS hc inverseSize ℓ hℓ ρ w τ t η)
    a ha hθ hstrict hag _ _ u f hf hproj
  · intro i
    filter_upwards [hcomp i] with x hx using hx.1
  · intro i
    apply M.gradedReciprocalWeight_cell_bound hS hc inverseSize ℓ hℓ ρ w τ t η (ha i) i
    filter_upwards [hcomp i] with x hx using hx.2

end Carleman
