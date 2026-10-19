module

public import Carleman.Spatial.DirichletWeakSolve
public import Carleman.Spatial.DirichletExtensionPairing

/-! All inner-domain weak Dirichlet solutions share an H¹ bound depending
only on the outer domain and the original L² load. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem dirichlet_subdomain_energy_bound (hT : IsOpen T) (hTS : T ⊆ S)
    (i : Fin d) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ S, |x i| ≤ R)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u (subdomainLp hTS f)) :
    ‖WeakSobolevJet.field 0 (WeakSobolevJet.extendDirichlet S hT u hu)‖^2 +
      ‖WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT u hu)‖^2 ≤
      (((2*R)^2+2*R)*‖f‖)^2 := by
  rw [WeakSobolevJet.extendDirichlet_field_norm hT hTS,
    WeakSobolevJet.extendDirichlet_field_norm hT hTS]
  apply (dirichlet_weak_solution_energy_bound hT i hR0 (fun x hx => hR x (hTS hx)) u hu _ hf).trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  exact mul_le_mul_of_nonneg_left (subdomainLp_norm_le hTS f) (by positivity)

theorem exists_uniform_dirichlet_subdomain_solutions (hd : 0 < d)
    (hb : Bornology.IsBounded S) (f : Lp ℝ 2 (volume.restrict S)) :
    ∃ C ≥ (0 : ℝ), ∀ (T : Set (SpatialCoordinates d)) (hT : IsOpen T) (hTS : T ⊆ S),
      ∃ u : WeakSobolevJet d 1 (volume.restrict T) T,
        ∃ hu : u ∈ dirichletJetSpace T, IsWeakNegativeLaplacian u (subdomainLp hTS f) ∧
          ‖WeakSobolevJet.field 0 (WeakSobolevJet.extendDirichlet S hT u hu)‖^2 +
          ‖WeakSobolevJet.field 1 (WeakSobolevJet.extendDirichlet S hT u hu)‖^2 ≤ C^2 := by
  obtain ⟨R,hR0,hR⟩ := hb.exists_pos_norm_le
  let i : Fin d := ⟨0,hd⟩
  have hr : ∀ x ∈ S, |x i| ≤ R := fun x hx =>
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans (hR x hx)
  refine ⟨((2*R)^2+2*R)*‖f‖,by positivity,?_⟩
  intro T hT hTS
  obtain ⟨u,hu,huf⟩ := exists_dirichlet_weak_solution hT hd (hb.subset hTS) (subdomainLp hTS f)
  exact ⟨u,hu,huf,dirichlet_subdomain_energy_bound hT hTS i hR0.le hr u hu f huf⟩

end Carleman
