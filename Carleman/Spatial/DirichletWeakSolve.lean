module

public import Carleman.Spatial.DirichletDistribution

/-! Actual weak Dirichlet solutions and quantitative first-order bounds.
Existence is constructed from the coercive form, and the estimates follow
from the original variational equation and the proved slab Poincare bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_weak_solution (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (f : Lp ℝ 2 (volume.restrict S)) :
    ∃ u : WeakSobolevJet d 1 (volume.restrict S) S,
      u ∈ dirichletJetSpace S ∧ IsWeakNegativeLaplacian u f := by
  let a := boundedDirichletOriginalForm hS hd hb
  let z := a.model.resolvent 0 le_rfl f
  have hz : a.model.operator z = f := by
    simpa only [zero_smul,add_zero] using a.model.resolvent_equation 0 le_rfl f
  obtain ⟨u,_,hu,huf⟩ := (dirichlet_operator_graph_iff hS hd hb (z : Lp ℝ 2 (volume.restrict S)) f).mp
    ⟨z,rfl,hz⟩
  exact ⟨u,hu,huf⟩

theorem dirichlet_weak_solution_gradient_bound (hS : IsOpen S) (i : Fin d) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ S, |x i| ≤ R)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ‖WeakSobolevJet.field 1 u‖ ≤ 2*R*‖f‖ := by
  have he := (isWeakNegativeLaplacian_iff_dirichlet hS u f).mp hf u hu
  rw [weakGradientPairing_apply,real_inner_self_eq_norm_sq] at he
  have hp := dirichlet_poincare hS i hR0 hR u hu
  have hb := (real_inner_le_norm f (WeakSobolevJet.value u)).trans
    (mul_le_mul_of_nonneg_left hp (norm_nonneg f))
  rw [← he] at hb
  by_contra hn
  have hg : 0 < ‖WeakSobolevJet.field 1 u‖ :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2*R*‖f‖) (lt_of_not_ge hn)
  nlinarith

theorem dirichlet_weak_solution_energy_bound (hS : IsOpen S) (i : Fin d) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ S, |x i| ≤ R)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ‖WeakSobolevJet.field 0 u‖^2 + ‖WeakSobolevJet.field 1 u‖^2 ≤
      (((2*R)^2+2*R)*‖f‖)^2 := by
  have hg := dirichlet_weak_solution_gradient_bound hS i hR0 hR u hu f hf
  have hv := (dirichlet_poincare hS i hR0 hR u hu).trans
    (mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2*R))
  have hg2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*R*‖f‖)).mpr hg
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*R*(2*R*‖f‖))).mpr hv
  rw [WeakSobolevJet.norm_zero_field]
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2*R)^3) (sq_nonneg ‖f‖)]

end Carleman
