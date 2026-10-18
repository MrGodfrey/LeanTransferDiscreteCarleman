module

public import Carleman.Spatial.WeightedMassAbsorption

/-! A genuine weighted projection estimate when its full-space output has nodal data.
The nodal representation and zero boundary data remain explicit obligations. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem weighted_projection_bound_of_nodal_representation
    (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (w ξ : BoundedMultiplier (volume.restrict S))
    (hrecip : ∀ᵐ x ∂volume.restrict S, w.value x*ξ.value x=1)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {θ : ℝ} (hθ : 1 ≤ θ) (hΓ : θ < p1GradingLimit d)
    (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j)
    (hw : ∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |w.value x| ≤ θ*a i)
    (hξ : ∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |ξ.value x| ≤ θ/a i)
    (u : Lp ℝ 2 (volume.restrict S)) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0)
    (hproj : ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
      Lp ℝ 2 (volume.restrict S)) = M.nodalLp hS.measurableSet hM f) :
    w.seminorm ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
      Lp ℝ 2 (volume.restrict S)) ≤
      (θ^3*(d+2)/p1MassMargin d θ)*w.seminorm u := by
  let ω := M.nodalWeightMinimum a
  let z := M.nodalLp hS.measurableSet hM f
  let q := M.nodalLp hS.measurableSet hM (fun x => (ω x)^2*f x)
  let X := M.conformingSpace (dirichletSubspace S)
  have hq : q ∈ X := M.nodal_squared_weight_test_mem hS hc hM hB ω f hf
  have hpair : inner ℝ z q = inner ℝ u q := by
    have h := X.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨q,hq⟩ u
    change inner ℝ (X.orthogonalProjectionOnto u : Lp ℝ 2 (volume.restrict S)) q = inner ℝ u q at h
    rw [hproj] at h
    exact h
  have hm := M.nodal_weighted_pairing_coercive hS hc hM a ha hθ hg f
  change p1MassMargin d θ*M.nodalCoefficientEnergy ω f ≤ inner ℝ z q at hm
  have hp : p1MassMargin d θ*M.nodalCoefficientEnergy ω f ≤ w.seminorm u*ξ.seminorm q :=
    hm.trans (hpair.le.trans (w.inner_le_weighted_pair ξ hrecip u q))
  rw [hproj]
  exact weighted_mass_norm_absorption
    (norm_nonneg (w.map z)) (norm_nonneg (w.map u)) (norm_nonneg (ξ.map q))
    (M.nodalCoefficientEnergy_nonneg ω f) (p1MassMargin_pos hθ hΓ)
    (zero_lt_one.trans_le hθ) (by positivity) hp
    (M.nodal_weighted_state_bound hS hc hM w a ha (zero_lt_one.trans_le hθ) hg hw f)
    (M.nodal_weighted_test_bound hS hc hM ξ a ha (zero_lt_one.trans_le hθ) hg hξ f)

end Carleman.SimplicialPartition
