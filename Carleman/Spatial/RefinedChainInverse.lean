module

public import Carleman.Spatial.UniformLinearProlongation

/-! The one-dimensional physical diagonal mass inverse inequality for all
zero-boundary coarse nodal values and every positive integer refinement. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

theorem trapezoid_square_sum (n : ℕ) (z : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, ((z k)^2+(z (k+1))^2)/2) =
      (∑ k ∈ Finset.range n, (z k)^2)+((z n)^2-(z 0)^2)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]; ring

theorem uniformLinearProlongation_inverse (m K : ℕ) (hm : 0 < m) (u : ℕ → ℝ)
    (h0 : u 0=0) (hK : u K=0) :
    (∑ k ∈ Finset.range (m*K),
      (uniformLinearProlongation m u (k+1)-uniformLinearProlongation m u k)^2) ≤
      12/(m:ℝ)^2*(∑ k ∈ Finset.range (m*K), (uniformLinearProlongation m u k)^2) := by
  have hmass : (∑ j ∈ Finset.range K, linearRefinementMass m (u j) (u (j+1))) =
      ∑ k ∈ Finset.range (m*K), (uniformLinearProlongation m u k)^2 := by
    rw [← uniformLinearProlongation_mass_cells m K hm u,trapezoid_square_sum,
      uniformLinearProlongation_node m hm u K]
    have he : uniformLinearProlongation m u 0=u 0 := by
      simpa only [Nat.mul_zero] using uniformLinearProlongation_node m hm u 0
    rw [he,h0,hK]
    ring
  rw [uniformLinearProlongation_energy_cells m K hm u,← hmass,Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => linearRefinement_inverse m hm (u j) (u (j+1))

theorem uniformLinearProlongation_physical_inverse (m K : ℕ) (hm : 0 < m)
    (u : ℕ → ℝ) (h0 : u 0=0) (hK : u K=0) {h : ℝ} (hh : 0 < h) :
    h*(∑ k ∈ Finset.range (m*K),
      ((uniformLinearProlongation m u (k+1)-uniformLinearProlongation m u k)/h)^2) ≤
      12/((m:ℝ)*h)^2*(h*∑ k ∈ Finset.range (m*K), (uniformLinearProlongation m u k)^2) := by
  calc
    _ = h⁻¹*(∑ k ∈ Finset.range (m*K),
        (uniformLinearProlongation m u (k+1)-uniformLinearProlongation m u k)^2) := by
      simp only [div_pow,← Finset.sum_div]
      field_simp
    _ ≤ h⁻¹*(12/(m:ℝ)^2*(∑ k ∈ Finset.range (m*K), (uniformLinearProlongation m u k)^2)) :=
      mul_le_mul_of_nonneg_left (uniformLinearProlongation_inverse m K hm u h0 hK) (inv_nonneg.mpr hh.le)
    _ = _ := by
      field_simp

end Carleman
