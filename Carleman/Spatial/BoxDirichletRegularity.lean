module

public import Carleman.Spatial.BoxPoissonRegularity
public import Carleman.Spatial.DirichletWeakSolve

/-! The actual Dirichlet operator on a positive coordinate box has precisely
H2 intersect H1_0 as domain, with a full H2 estimate by its original L2 load. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem box_dirichlet_domain_le_h2 (hd : 0 < d) (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) :
    (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b)).model.domain ≤
      sobolevSubspace d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b) := by
  intro z hz
  let A := boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)
  let f := A.model.operator ⟨z,hz⟩
  obtain ⟨u,huz,hu,huf⟩ := (dirichlet_operator_graph_iff (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) z f).mp ⟨⟨z,hz⟩,rfl,rfl⟩
  obtain ⟨C,hC,hbound⟩ := exists_box_dirichlet_H2_bound a b hpos
  obtain ⟨v,hv,_,_⟩ := hbound u hu f huf
  refine ⟨v,?_⟩
  have he := congrArg (fun w => WeakSobolevJet.value w) hv
  exact he.trans huz

theorem box_dirichlet_domain_eq_h2 (hd : 0 < d) (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) :
    (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b)).model.domain =
      sobolevSubspace d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b) ⊓
        dirichletSubspace (openCoordinateBox a b) :=
  le_antisymm (le_inf (box_dirichlet_domain_le_h2 hd a b hpos)
    (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b)).domain_le)
    (h2_dirichlet_le_domain (openCoordinateBox_isOpen a b) hd (openCoordinateBox_isBounded a b))

theorem exists_box_dirichlet_H2_estimate (hd : 0 < d) (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
      u ∈ dirichletJetSpace (openCoordinateBox a b) →
      ∀ f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b)), IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b),
        WeakSobolevJet.truncate (by decide : 1 ≤ 2) v=u ∧ negativeLaplacian v=f ∧ ‖v‖ ≤ K*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_box_dirichlet_H2_bound a b hpos
  obtain ⟨R,hR0,hR⟩ := (openCoordinateBox_isBounded a b).exists_pos_norm_le
  let i : Fin d := ⟨0,hd⟩
  have hr : ∀ x ∈ openCoordinateBox a b, |x i| ≤ R := fun x hx =>
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  let B : ℝ := 1+2*R+(2*R)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(2*R)^2+2*R+Real.sqrt C*B,by positivity,?_⟩
  intro u hu f hf
  obtain ⟨v,hv,hvf,hvn⟩ := hbound u hu f hf
  have hG := dirichlet_weak_solution_gradient_bound (openCoordinateBox_isOpen a b) i hR0.le hr u hu f hf
  have hV := (dirichlet_poincare (openCoordinateBox_isOpen a b) i hR0.le hr u hu).trans
    (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 2*R))
  have hN : ‖f‖+‖WeakSobolevJet.field 1 u‖+‖WeakSobolevJet.value u‖ ≤ B*‖f‖ := by
    dsimp [B]
    nlinarith
  have hH : ‖WeakSobolevJet.field 2 v‖ ≤ Real.sqrt C*(B*‖f‖) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hC]
    exact hvn.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by positivity) (by positivity)).mpr hN) hC)
  have h0 : WeakSobolevJet.field 0 v=WeakSobolevJet.field 0 u :=
    congrArg (fun w => WeakSobolevJet.field (0 : Fin 2) w) hv
  have h1 : WeakSobolevJet.field 1 v=WeakSobolevJet.field 1 u :=
    congrArg (fun w => WeakSobolevJet.field (1 : Fin 2) w) hv
  refine ⟨v,hv,hvf,?_⟩
  have hh := WeakSobolevJet.norm_le_sum_fields v
  rw [Fin.sum_univ_three,h0,WeakSobolevJet.norm_zero_field,h1] at hh
  nlinarith

end Carleman
