module

public import Carleman.Weights.FullNodalResidual
public import Carleman.Spatial.NodalResidualSobolev

/-! The full conforming-state nodal residual is an actual weak H¹ jet;
both sides of the global weighted estimates use genuine weak-state fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_full_weak_residual
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {κ : ℝ} (hκ : 0 ≤ κ)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    ∀ hM : M.FaceMatching, M.BoundaryFitted →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → M.maxDiameter*q ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
    ∀ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
    ∃ (f : SpatialCoordinates d → ℝ) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      (∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) ∧
      WeakSobolevJet.value u=M.nodalLp hS.measurableSet hM f ∧
      let w := allowedSquaredWeight ρ q τ η
      let energy := q^4*(∫ x in S, w x*(WeakSobolevJet.value u x)^2)+
        q^2*(∫ x in S, w x*‖WeakSobolevJet.field 1 u x‖^2)
      WeakSobolevJet.value e =ᵐ[volume.restrict S] M.nodalProductResidual w f ∧
      M.nodalLp hS.measurableSet hM (fun x => w x*f x) ∈
        M.conformingSpace (dirichletSubspace S) ∧
      (∫ x in S, (WeakSobolevJet.value e x)^2/w x) ≤ C*M.maxDiameter^4*energy ∧
      (∫ x in S, ‖WeakSobolevJet.field 1 e x‖^2/w x) ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_full_nodal_residual hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM hB q hq τ η hη hsmall a r hr hball hshape u hu
  obtain ⟨f,hf,hval,hI,hvalue,hgradient⟩ := hbound M hM hB q hq τ η hη hsmall a r hr hball hshape u hu
  obtain ⟨e,he,hd⟩ := M.squared_nodal_residual_weak_jet hS hc hcompact hM hB hρ q τ η f hf
  refine ⟨f,e,hf,hval,he,hI,?_,?_⟩
  · calc
      _ = ∫ x in S, (M.nodalProductResidual (allowedSquaredWeight ρ q τ η) f x)^2/
          allowedSquaredWeight ρ q τ η x := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
      _ ≤ _ := hvalue
  · calc
      _ = ∫ x in S, ‖derivativeOneFiber (fderiv ℝ (M.nodalProductResidual (allowedSquaredWeight ρ q τ η) f) x)‖^2/
          allowedSquaredWeight ρ q τ η x := by
        apply integral_congr_ae
        filter_upwards [hd] with x hx
        rw [hx]
      _ ≤ _ := hgradient

end Carleman
