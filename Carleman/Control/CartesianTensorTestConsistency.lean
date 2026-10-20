module

public import Carleman.Control.CartesianTestStrongConvergence
public import Carleman.Control.TensorTimeTests

/-! Original sampled finite tensor tests, full time differences and endpoints. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}
def cartesianBoxDirichletLinearMap (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) :
    CartesianPhysicalState δ hδ N →ₗ[ℝ] DirichletEnergyState (openCoordinateBox lo hi) where
  toFun := cartesianBoxDirichletState lo hi δ hδ N hbox
  map_add' := by
    intro f g
    apply conformingEmbed_injective (dirichletSubspace (openCoordinateBox lo hi))
      (openCoordinateBox_isOpen _ _) (ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet)
    change dirichletStateValue _ _=dirichletStateValue _ _
    rw [map_add]
    simp only [cartesianBoxDirichletState_value]
    have he := funext hbox
    subst hi
    change WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N (f+g))=
      WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N f)+
      WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N g)
    simp only [cartesianKuhnReconstructionJet_value]
    exact (cartesianPhysicalReconstructionLp lo δ hδ N).map_add f g
  map_smul' := by
    intro c f
    apply conformingEmbed_injective (dirichletSubspace (openCoordinateBox lo hi))
      (openCoordinateBox_isOpen _ _) (ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet)
    change dirichletStateValue _ _=dirichletStateValue _ _
    rw [map_smul]
    simp only [cartesianBoxDirichletState_value]
    have he := funext hbox
    subst hi
    change WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N (c • f))=
      c • WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N f)
    simp only [cartesianKuhnReconstructionJet_value]
    exact (cartesianPhysicalReconstructionLp lo δ hδ N).map_smul c f

theorem cartesianBoxDirichletLinearMap_apply (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (f : CartesianPhysicalState δ hδ N) :
    cartesianBoxDirichletLinearMap lo hi δ hδ N hbox f=cartesianBoxDirichletState lo hi δ hδ N hbox f := rfl

theorem cartesianNodalSample_finite (lo δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) {L : Type*} [Fintype L] (c : L → ℝ) (ψ : L → SpatialCoordinates d → ℝ) :
    cartesianNodalSample lo δ hδ N (fun x => ∑ l, c l*ψ l x)=
      ∑ l, c l • cartesianNodalSample lo δ hδ N (ψ l) := by
  apply PhysicalFiniteSpace.valuesEquiv.injective
  rw [map_sum]
  simp only [map_smul]
  funext a
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rfl

theorem cartesian_finite_time_test_H1_consistency (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n)
        (cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l ((g n).nodeTime i)*(ψ l).value x)))) atTop
      (𝓝 (∑ l, timeTensor T (ψ l).dirichletState ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n)
        ((g n).dt⁻¹ • (cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l (((i.val:ℝ)+1)*(g n).dt)*(ψ l).value x)-
          cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l ((i.val:ℝ)*(g n).dt)*(ψ l).value x))))) atTop
      (𝓝 (∑ l, timeTensor T (ψ l).dirichletState ((continuous_time_memLp T (f l) (hf l)).toLp (f l)))) := by
  have ht := finite_tensor_time_test_consistency T hTpos g hT htlim η f hη hf hd
    (fun l n => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) (ψ l).value))
    (fun l => (ψ l).dirichletState)
    (fun l => cartesian_test_H1_strong_convergence lo hi δ hδ N hbox h hh hκ hlower hupper hlim (ψ l))
  simp only [cartesianNodalSample_finite, ← cartesianBoxDirichletLinearMap_apply,map_smul,map_sub,map_sum]
  exact ht

theorem cartesian_finite_time_test_cell_L2_consistency (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
        (cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l ((g n).nodeTime i)*(ψ l).value x)))) atTop
      (𝓝 (∑ l, timeTensor T ((ψ l).toLp (volume.restrict (openCoordinateBox lo hi))) ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
        ((g n).dt⁻¹ • (cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l (((i.val:ℝ)+1)*(g n).dt)*(ψ l).value x)-
          cartesianNodalSample lo (δ n) (hδ n) (N n)
          (fun x => ∑ l, η l ((i.val:ℝ)*(g n).dt)*(ψ l).value x))))) atTop
      (𝓝 (∑ l, timeTensor T ((ψ l).toLp (volume.restrict (openCoordinateBox lo hi))) ((continuous_time_memLp T (f l) (hf l)).toLp (f l)))) := by
  have ht := finite_tensor_time_test_consistency T hTpos g hT htlim η f hη hf hd
    (fun l n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) (ψ l).value))
    (fun l => ((ψ l).toLp (volume.restrict (openCoordinateBox lo hi))))
    (fun l => cartesian_test_cell_L2_strong_convergence lo hi δ hδ N hbox h hh hκ hlower hupper hlim (ψ l))
  simp only [cartesianNodalSample_finite,map_smul,map_sub,map_sum]
  exact ht

theorem cartesian_finite_test_endpoint_consistency (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi)) (τ : ℝ) :
    Tendsto (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) (fun x => ∑ l, η l τ*(ψ l).value x))) atTop
      (𝓝 (∑ l, η l τ • (ψ l).toLp (volume.restrict (openCoordinateBox lo hi)))) := by
  simp only [cartesianNodalSample_finite,map_sum,map_smul]
  exact finite_tensor_test_endpoint_consistency η
    (fun l n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) (ψ l).value))
    (fun l => (ψ l).toLp (volume.restrict (openCoordinateBox lo hi)))
    (fun l => cartesian_test_cell_L2_strong_convergence lo hi δ hδ N hbox h hh hκ hlower hupper hlim (ψ l)) τ

end Carleman
