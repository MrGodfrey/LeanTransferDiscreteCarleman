module

public import Carleman.Transfer.ScalePowers

/-! Original approximation rates imply the two squared error budgets without
changing their spatial or temporal orders. -/
@[expose] public noncomputable section
namespace Carleman
namespace ErrorScales
variable (e : ErrorScales) (g : TimeGrid) (m : ℕ) (C h : ℝ)

def approximationConstant : ℝ := 8*C^2+2*(C+C^2)^2+2

theorem approximationConstant_pos : 0 < approximationConstant C := by
  unfold approximationConstant
  positivity

theorem approximation_rates (hC : 0 ≤ C) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hE : e.aE ≤ C*h^m) (h0 : e.a₀+e.ηA ≤ C*h^(2*m)) :
    (e.energy g)^2 ≤ approximationConstant C*(h^(2*m)+g.dt) ∧
    (e.l2 g)^2 ≤ approximationConstant C*(h^(4*m)+g.dt^2) := by
  have hdt := g.dt_pos.le
  have hη : e.ηA ≤ C*h^(2*m) := (le_add_of_nonneg_left e.a₀_nonneg).trans h0
  have hp : 0 ≤ h^m := pow_nonneg hh _
  have hp1 : h^m ≤ 1 := pow_le_one₀ hh hh1
  have hp2 : h^(2*m) = (h^m)^2 := by rw [← pow_mul]; congr 1; omega
  have hp4 : h^(4*m) = (h^(2*m))^2 := by rw [← pow_mul]; congr 1; omega
  have hp21 : h^(2*m) ≤ h^m := by rw [hp2]; nlinarith
  have hη' := hη.trans (mul_le_mul_of_nonneg_left hp21 hC)
  have hEn : 0 ≤ e.energy g := by
    dsimp [energy]; exact add_nonneg (add_nonneg e.aE_nonneg e.ηA_nonneg) (Real.sqrt_nonneg _)
  have hEb : e.energy g ≤ 2*C*h^m+Real.sqrt g.dt := by dsimp [energy]; linarith
  have hsqdt := Real.sq_sqrt g.dt_pos.le
  have hsE : (e.energy g)^2 ≤ 8*C^2*h^(2*m)+2*g.dt := by
    rw [hp2]
    have hs := (sq_le_sq₀ hEn (by positivity)).mpr hEb
    nlinarith only [hs,sq_nonneg (2*C*h^m-Real.sqrt g.dt),hsqdt]
  have haEsq : e.aE^2 ≤ C^2*h^(2*m) := by
    have hh := (sq_le_sq₀ e.aE_nonneg (mul_nonneg hC hp)).mpr hE
    simpa only [mul_pow,hp2] using hh
  have h0n : 0 ≤ e.l2 g := by
    dsimp [l2]; exact add_nonneg (add_nonneg (add_nonneg e.a₀_nonneg (sq_nonneg _)) e.ηA_nonneg) g.dt_pos.le
  have h0b : e.l2 g ≤ (C+C^2)*h^(2*m)+g.dt := by dsimp [l2]; nlinarith only [h0,haEsq]
  have hs0 : (e.l2 g)^2 ≤ 2*(C+C^2)^2*h^(4*m)+2*g.dt^2 := by
    rw [hp4]
    have hs := (sq_le_sq₀ h0n (by positivity)).mpr h0b
    nlinarith only [hs,sq_nonneg ((C+C^2)*h^(2*m)-g.dt)]
  have hME : 8*C^2 ≤ approximationConstant C := by dsimp [approximationConstant]; nlinarith [sq_nonneg C,sq_nonneg (C+C^2)]
  have hM0 : 2*(C+C^2)^2 ≤ approximationConstant C := by dsimp [approximationConstant]; nlinarith [sq_nonneg C,sq_nonneg (C+C^2)]
  have hM2 : 2 ≤ approximationConstant C := by dsimp [approximationConstant]; nlinarith [sq_nonneg C,sq_nonneg (C+C^2)]
  constructor
  · exact hsE.trans (by
      have h1 := mul_le_mul_of_nonneg_right hME (pow_nonneg hh (2*m))
      have h2 := mul_le_mul_of_nonneg_right hM2 g.dt_pos.le
      nlinarith only [h1,h2])
  · exact hs0.trans (by
      have h1 := mul_le_mul_of_nonneg_right hM0 (pow_nonneg hh (4*m))
      have h2 := mul_le_mul_of_nonneg_right hM2 (sq_nonneg g.dt)
      nlinarith only [h1,h2])

end ErrorScales
end Carleman
