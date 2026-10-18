module

public import Carleman.Weights.SquaredNodalGlobal
public import Carleman.Spatial.FullNodalGradient

/-! The actual full conforming H¹₀ state supplies a zero-boundary nodal
representative and test, with the original weak-state energy on the right. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_full_nodal_residual
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
    ∃ f : SpatialCoordinates d → ℝ,
      (∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) ∧
      WeakSobolevJet.value u=M.nodalLp hS.measurableSet hM f ∧
      let w := allowedSquaredWeight ρ q τ η
      let e := M.nodalProductResidual w f
      let energy := q^4*(∫ x in S, w x*(WeakSobolevJet.value u x)^2)+
        q^2*(∫ x in S, w x*‖WeakSobolevJet.field 1 u x‖^2)
      M.nodalLp hS.measurableSet hM (fun x => w x*f x) ∈
        M.conformingSpace (dirichletSubspace S) ∧
      (∫ x in S, (e x)^2/w x) ≤ C*M.maxDiameter^4*energy ∧
      (∫ x in S, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) ≤ C*M.maxDiameter^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_nodal_global_integrals hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM hB q hq τ η hη hsmall a r hr hball hshape u hu
  obtain ⟨f,hf,hval,hgrad⟩ := M.conforming_dirichlet_nodal_with_gradient hS hc hM u hu
  refine ⟨f,hf,hval,M.weighted_nodal_mem_dirichletConformingSpace hS hc hM hB _ f hf,?_⟩
  let w := allowedSquaredWeight ρ q τ η
  have hv : (∫ x in S, w x*(WeakSobolevJet.value u x)^2) =
      ∫ x in S, w x*(M.nodalFunction f x)^2 := by
    rw [hval]
    apply integral_congr_ae
    filter_upwards [M.nodalLp_ae hS.measurableSet hM f] with x hx
    rw [hx]
  have hg : (∫ x in S, w x*‖WeakSobolevJet.field 1 u x‖^2) =
      ∫ x in S, w x*‖derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)‖^2 := by
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx]
  change (∫ x in S, (M.nodalProductResidual w f x)^2/w x) ≤ C*M.maxDiameter^4*
      (q^4*(∫ x in S, w x*(WeakSobolevJet.value u x)^2)+q^2*(∫ x in S, w x*‖WeakSobolevJet.field 1 u x‖^2)) ∧ _
  rw [hv,hg]
  exact hbound M hM q hq τ η hη hsmall a r hr hball hshape f

end Carleman
