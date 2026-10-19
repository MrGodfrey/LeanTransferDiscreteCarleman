module

public import Carleman.Spatial.CartesianCoarseProlongation
public import Carleman.Control.FilterRayleighBound

/-! Proposition 7.8: the actual tensor-product coarse-grid range has Rayleigh
quotient at most twelve times the sum of the inverse coarse step squares. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {d : ℕ}

def cartesianCoarseFilter (h : Fin d → ℝ) (hh : ∀ r, 0 < h r) (m K : Fin d → ℕ) :
    Submodule ℝ (CartesianPhysicalState h hh (fun r => m r*K r)) :=
  (cartesianCoarseProlongation h hh m K).range

theorem cartesian_coarse_energy_bound (o h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ) :
    inner ℝ (cartesianPhysicalLaplacian o h hh (fun r => m r*K r)
      (cartesianCoarseProlongation h hh m K u)) (cartesianCoarseProlongation h hh m K u) ≤
      (12*∑ r, ((m r:ℝ)*h r)⁻¹^2)*‖cartesianCoarseProlongation h hh m K u‖^2 := by
  rw [cartesianCoarseProlongation_energy o h hh m K hm,
    cartesianCoarseProlongation_mass h hh m K hm]
  have hb := mul_le_mul_of_nonneg_left (tensorLinearProlongation_inverse m K hm u h hh)
    (show 0 ≤ ∏ r, h r from Finset.prod_nonneg (fun r _ => (hh r).le))
  have hc : (∑ r, 12/((m r:ℝ)*h r)^2)=12*∑ r, ((m r:ℝ)*h r)⁻¹^2 := by
    simp only [Finset.mul_sum,div_eq_mul_inv,inv_pow]
  rw [hc] at hb
  simpa only [mul_left_comm] using hb

theorem fd_coarse_filter_rayleigh (o h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r) :
    filterRayleigh (cartesianPhysicalLaplacian o h hh (fun r => m r*K r))
      (cartesianCoarseFilter h hh m K) ≤ 12*∑ r, ((m r:ℝ)*h r)⁻¹^2 := by
  apply filterRayleigh_le_of_energy_bound _ _ (by positivity)
  rintro x ⟨u,rfl⟩
  exact cartesian_coarse_energy_bound o h hh m K hm u

/-- The original divisibility formulation supplies the very same interpolation,
identified at every fine interior node, for every allowed nested grid. -/
theorem fd_dividing_filter_rayleigh (o h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (N m : Fin d → ℕ) (hm : ∀ r, 0 < m r) (hdiv : ∀ r, m r ∣ N r) :
    ∃ I : (CartesianInteriorIndex (fun r => N r/m r) → ℝ) →ₗ[ℝ]
        CartesianPhysicalState h hh N,
      (∀ u a, I u a=tensorLinearProlongation m (fun r => N r/m r) u (fun r => (a r).val+1)) ∧
      filterRayleigh (cartesianPhysicalLaplacian o h hh N) I.range ≤
        12*∑ r, ((m r:ℝ)*h r)⁻¹^2 := by
  let K := fun r => N r/m r
  have hNK : N=(fun r => m r*K r) := funext fun r => (Nat.mul_div_cancel' (hdiv r)).symm
  change ∃ I : (CartesianInteriorIndex K → ℝ) →ₗ[ℝ] CartesianPhysicalState h hh N,
    (∀ u a, I u a=tensorLinearProlongation m K u (fun r => (a r).val+1)) ∧
    filterRayleigh (cartesianPhysicalLaplacian o h hh N) I.range ≤ _
  rw [hNK]
  exact ⟨cartesianCoarseProlongation h hh m K,fun _ _ => rfl,
    fd_coarse_filter_rayleigh o h hh m K hm⟩

end Carleman.Physical
