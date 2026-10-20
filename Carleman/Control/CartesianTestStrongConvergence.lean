module

public import Carleman.Control.CartesianTestInterpolation
public import Carleman.Control.P1TestStrongConvergence

/-! Strong convergence of original finite-difference test reconstructions in H¹₀ and L². -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}
theorem cartesian_test_H1_strong_convergence (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (φ : SpatialTest (openCoordinateBox lo hi)) :
    Tendsto (fun n => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) φ.value)) atTop (𝓝 φ.dirichletState) := by
  let M := fun n => cartesianBoxKuhnPartition lo hi (δ n) (hδ n) (N n) (hbox n)
  obtain ⟨C,hC,hballs⟩ := cartesianBoxKuhn_uniform_inballs (d := d) κ hκ
  have he n := hballs lo hi (δ n) (hδ n) (N n) (hbox n) (h n) (hh n) (hlower n) (hupper n)
  choose a r hr hball hshape using he
  have hd : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0) :=
    squeeze_zero (fun n => (M n).maxDiameter_nonneg)
      (fun n => cartesianBoxKuhnPartition_maxDiameter_le lo hi (δ n) (hδ n) (N n) (hbox n)
        (h n) (hh n) (hupper n)) (by simpa using tendsto_const_nhds.mul hlim)
  simp_rw [cartesianBoxDirichletState_test_eq_nodal]
  exact full_p1_test_H1_strong_convergence (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex _ _) M
    (fun n => cartesianBoxKuhnPartition_faceMatching lo hi (δ n) (hδ n) (N n) (hbox n))
    (fun n => cartesianBoxKuhnPartition_boundaryFitted lo hi (δ n) (hδ n) (N n) (hbox n))
    hC.le a (fun n _ => r n) (fun n _ => hr n) hball hshape hd φ

theorem cartesian_test_cell_L2_strong_convergence (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (φ : SpatialTest (openCoordinateBox lo hi)) :
    Tendsto (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      (cartesianNodalSample lo (δ n) (hδ n) (N n) φ.value)) atTop
      (𝓝 (φ.toLp (volume.restrict (openCoordinateBox lo hi)))) := by
  let S := openCoordinateBox lo hi
  let v := fun n => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n)
    (cartesianNodalSample lo (δ n) (hδ n) (N n) φ.value)
  let E := fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
    (cartesianNodalSample lo (δ n) (hδ n) (N n) φ.value)
  have hv : Tendsto v atTop (𝓝 φ.dirichletState) :=
    cartesian_test_H1_strong_convergence lo hi δ hδ N hbox h hh hκ hlower hupper hlim φ
  have hg := (((dirichletStateGradient S).continuous.tendsto _).comp hv).norm
  obtain ⟨C,hC,hbound⟩ := cartesianBoxCell_kuhn_L2_consistency (d := d)
  have he : Tendsto (fun n => E n-dirichletStateValue S (v n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => hbound lo hi (δ n) (hδ n) (N n) (hbox n) (h n) (hh n).le (hupper n) _)
    simpa only [Function.comp_apply,v,S,cartesianBoxDirichletState_gradient,mul_zero,zero_mul] using (tendsto_const_nhds.mul hlim).mul hg
  have hval := ((dirichletStateValue S).continuous.tendsto _).comp hv
  have ht := he.add hval
  simpa only [Function.comp_apply,sub_add_cancel,zero_add,SpatialTest.dirichletState_value] using ht

end Carleman
