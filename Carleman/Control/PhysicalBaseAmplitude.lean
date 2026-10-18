module

public import Carleman.Control.PhysicalWeightSecond

/-! The original base amplitude, with constants chosen before T and M. -/
@[expose] public noncomputable section
namespace Carleman.Physical

def physicalBaseAmplitude (Cb qc T M : ℝ) : ℝ := Cb*(qc+T⁻¹+M^(2/3:ℝ))

theorem physicalBaseAmplitude_bounds (Cb qc T M : ℝ)
    (hCb : 0 ≤ Cb) (hqc : 0 ≤ qc) (hT : 0 < T) (hM : 0 ≤ M) :
    Cb*qc ≤ physicalBaseAmplitude Cb qc T M ∧
    Cb ≤ physicalBaseAmplitude Cb qc T M*T ∧
    Cb^3*M^2 ≤ physicalBaseAmplitude Cb qc T M^3 := by
  have hp : 0 ≤ M^(2/3:ℝ) := Real.rpow_nonneg hM _
  have ht : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  have hc : Cb*qc ≤ physicalBaseAmplitude Cb qc T M := by
    dsimp only [physicalBaseAmplitude]
    exact mul_le_mul_of_nonneg_left (by linarith only [ht,hp]) hCb
  have hi : Cb*T⁻¹ ≤ physicalBaseAmplitude Cb qc T M := by
    dsimp only [physicalBaseAmplitude]
    exact mul_le_mul_of_nonneg_left (by linarith only [hqc,hp]) hCb
  have hm : Cb*M^(2/3:ℝ) ≤ physicalBaseAmplitude Cb qc T M := by
    dsimp only [physicalBaseAmplitude]
    exact mul_le_mul_of_nonneg_left (by linarith only [hqc,ht]) hCb
  have he : (M^(2/3:ℝ))^3 = M^2 := by
    rw [← Real.rpow_mul_natCast hM]
    norm_num
  refine ⟨hc,?_,?_⟩
  · simpa only [mul_assoc,inv_mul_cancel₀ (ne_of_gt hT),mul_one] using
      mul_le_mul_of_nonneg_right hi hT.le
  · have hh := pow_le_pow_left₀ (mul_nonneg hCb hp) hm 3
    simpa only [mul_pow,he] using hh

theorem physicalBaseAmplitude_ge_two (Cb qc T M : ℝ)
    (hCb : 2 ≤ Cb) (hqc : 1 ≤ qc) (hT : 0 < T) (hM : 0 ≤ M) :
    2 ≤ physicalBaseAmplitude Cb qc T M ∧ 2*qc ≤ physicalBaseAmplitude Cb qc T M := by
  have hc := (physicalBaseAmplitude_bounds Cb qc T M (by linarith) (by linarith) hT hM).1
  have hh := mul_le_mul_of_nonneg_right hCb (show 0 ≤ qc by linarith)
  constructor <;> linarith only [hc,hh,hqc]

theorem physicalBaseAmplitude_derivative_budgets (Cb qc T M β : ℝ)
    (hCb : 0 ≤ Cb) (hqc : 1 ≤ qc) (hT : 0 < T) (hM : 0 ≤ M)
    (hβ : 0 < β) (hbudget : 2*Real.pi/β ≤ Cb) :
    Real.pi/(physicalBaseAmplitude Cb qc T M*T) ≤ β ∧
    4*Real.pi^2/(physicalBaseAmplitude Cb qc T M^2*T^2) ≤ β^2 := by
  have hb := (physicalBaseAmplitude_bounds Cb qc T M hCb (by linarith) hT hM).2.1
  have hCbpos : 0 < Cb := (div_pos (mul_pos (by norm_num) Real.pi_pos) hβ).trans_le hbudget
  have hprod : 0 < physicalBaseAmplitude Cb qc T M*T := hCbpos.trans_le hb
  have htwo : 2*Real.pi/(physicalBaseAmplitude Cb qc T M*T) ≤ β := by
    apply (div_le_iff₀ hprod).mpr
    have h1 := (div_le_iff₀ hβ).mp hbudget
    have h2 := mul_le_mul_of_nonneg_left hb hβ.le
    nlinarith only [h1,h2]
  constructor
  · have hp : 0 < Real.pi/(physicalBaseAmplitude Cb qc T M*T) := div_pos Real.pi_pos hprod
    rw [mul_div_assoc] at htwo
    linarith only [htwo,hp]
  · have hh := (sq_le_sq₀ (div_nonneg (by positivity) hprod.le) hβ.le).mpr htwo
    convert hh using 1
    ring

end Carleman.Physical
