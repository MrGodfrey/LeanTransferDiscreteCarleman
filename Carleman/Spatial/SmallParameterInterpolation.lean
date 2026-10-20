module

public import Carleman.Spatial.DomainJetInterpolation
public import Carleman.Spatial.ParameterConjugation
@[expose] public noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def lowerParameterNorm (q : ℝ) (u : WeakSobolevJet d n ν S) : ℝ :=
  ∑ k : Fin n, q^(n-k.val)*‖field k.castSucc u‖

theorem lowerParameterNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (u : WeakSobolevJet d n ν S) :
    0 ≤ lowerParameterNorm q u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hq _) (norm_nonneg _)

theorem lowerParameterNorm_rescale {q R : ℝ} (hq : 0 ≤ q) (hR : 1 ≤ R)
    (u : WeakSobolevJet d n ν S) :
    R*lowerParameterNorm q u ≤ parameterNorm (R*q) BoundedMultiplier.one u := by
  unfold lowerParameterNorm parameterNorm
  simp only [BoundedMultiplier.one_seminorm,Finset.mul_sum]
  rw [Fin.sum_univ_castSucc]
  apply le_trans (b := ∑ k : Fin n, (R*q)^(n-k.val)*‖field k.castSucc u‖)
  · apply Finset.sum_le_sum
    intro k _
    have hp : R ≤ R^(n-k.val) := by
      simpa only [pow_one] using pow_le_pow_right₀ hR (show 1 ≤ n-k.val by omega)
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hp
      (mul_nonneg (pow_nonneg hq (n-k.val)) (norm_nonneg (field k.castSucc u)))]
  · exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (mul_nonneg (zero_le_one.trans hR) hq) _) (norm_nonneg _))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundedLipschitz_lowerParameter_small (hS : IsBoundedLipschitzDomain S F)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      ∀ u : WeakSobolevJet d n (volume.restrict S) S,
      lowerParameterNorm q u ≤ η*‖u‖+C*q^n*‖value u‖ := by
  obtain ⟨I,hI,hbound⟩ := boundedLipschitz_parameter_interpolation hS n
  let R := max 1 (I/η)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hIR : I/R ≤ η := by
    apply (div_le_iff₀ hRp).mpr
    have he := (div_le_iff₀ hη).mp (le_max_right 1 (I/η))
    nlinarith
  let C := 1+I*R^n/R
  have hC : 1 ≤ C := le_add_of_nonneg_right (div_nonneg (mul_nonneg (zero_le_one.trans hI) (pow_nonneg hRp.le _)) hRp.le)
  refine ⟨C,hC,?_⟩
  intro q hq u
  have hRq : 1 ≤ R*q := one_le_mul_of_one_le_of_one_le hR hq
  have hb := hbound (R*q) hRq u
  have hs := lowerParameterNorm_rescale (zero_le_one.trans hq) hR u
  simp only [parameterNorm,BoundedMultiplier.one_seminorm] at hs
  have he : lowerParameterNorm q u ≤ I/R*‖u‖+(I*R^n/R)*q^n*‖value u‖ := by
    apply (mul_le_mul_iff_right₀ hRp).mp
    calc
      R*lowerParameterNorm q u ≤ I*(‖u‖+(R*q)^n*‖value u‖) := by nlinarith [hs.trans hb]
      _ = R*(I/R*‖u‖+(I*R^n/R)*q^n*‖value u‖) := by rw [mul_pow]; field_simp
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hIR (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show I*R^n/R ≤ C by dsimp [C]; linarith)
      (pow_nonneg (zero_le_one.trans hq) _)) (norm_nonneg _)))
theorem boundedLipschitz_lowerParameter_product_small (hS : IsBoundedLipschitzDomain S F)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      ∀ u : WeakSobolevJet d n (volume.restrict S) S,
      lowerParameterNorm q u*parameterNorm q BoundedMultiplier.one u ≤
        η*‖u‖^2+C*(q^n*‖value u‖)^2 := by
  obtain ⟨I,hI,hbound⟩ := boundedLipschitz_parameter_interpolation hS n
  let R := max 1 (2*I^2/η)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hIR : 2*I^2/R ≤ η := by
    apply (div_le_iff₀ hRp).mpr
    have he := (div_le_iff₀ hη).mp (le_max_right 1 (2*I^2/η))
    nlinarith
  let C := 1+2*I^2*(R^n)^2/R
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro q hq u
  have hq0 := zero_le_one.trans hq
  have hRq : 1 ≤ R*q := one_le_mul_of_one_le_of_one_le hR hq
  have hs := lowerParameterNorm_rescale hq0 hR u
  have hm := parameterNorm_mono hq0 (show q ≤ R*q by nlinarith) BoundedMultiplier.one u
  have hprod := mul_le_mul hs hm (parameterNorm_nonneg hq0 BoundedMultiplier.one u)
    (parameterNorm_nonneg (zero_le_one.trans hRq) BoundedMultiplier.one u)
  have hb : parameterNorm (R*q) BoundedMultiplier.one u ≤ I*(‖u‖+(R*q)^n*‖value u‖) := by
    simpa only [parameterNorm,BoundedMultiplier.one_seminorm] using hbound (R*q) hRq u
  have hsq := (sq_le_sq₀ (parameterNorm_nonneg (zero_le_one.trans hRq) BoundedMultiplier.one u)
    (mul_nonneg (zero_le_one.trans hI) (by positivity))).mpr hb
  have ha : R*(lowerParameterNorm q u*parameterNorm q BoundedMultiplier.one u) ≤
      2*I^2*(‖u‖^2+(R^n)^2*(q^n*‖value u‖)^2) := by
    have hh : (‖u‖+(R*q)^n*‖value u‖)^2 ≤ 2*(‖u‖^2+((R*q)^n*‖value u‖)^2) := by
      nlinarith [sq_nonneg (‖u‖-(R*q)^n*‖value u‖)]
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg I)
    simp only [mul_pow] at hsq hh'
    nlinarith [hprod]
  have he : lowerParameterNorm q u*parameterNorm q BoundedMultiplier.one u ≤
      (2*I^2/R)*‖u‖^2+(2*I^2*(R^n)^2/R)*(q^n*‖value u‖)^2 := by
    apply (mul_le_mul_iff_right₀ hRp).mp
    calc
      _ ≤ 2*I^2*(‖u‖^2+(R^n)^2*(q^n*‖value u‖)^2) := ha
      _ = _ := by field_simp
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_right hIR (sq_nonneg _))
    (mul_le_mul_of_nonneg_right (show 2*I^2*(R^n)^2/R ≤ C by dsimp [C]; linarith) (sq_nonneg _)))

theorem lowerOrderQuadratic_le {q : ℝ} (hq : 0 ≤ q) (u : WeakSobolevJet d n ν S) :
    (∑ k : Fin (n+1), ∑ j : Fin (n+1), if k.val+j.val < 2*n then
      q^(2*n-k.val-j.val)*‖field k u‖*‖field j u‖ else 0) ≤
    2*lowerParameterNorm q u*parameterNorm q BoundedMultiplier.one u := by
  let X := fun k : Fin (n+1) => q^(n-k.val)*‖field k u‖
  have hX (k) : 0 ≤ X k := mul_nonneg (pow_nonneg hq _) (norm_nonneg _)
  have hp (k j : Fin (n+1)) : q^(2*n-k.val-j.val)*‖field k u‖*‖field j u‖=X k*X j := by
    dsimp [X]
    rw [show 2*n-k.val-j.val=(n-k.val)+(n-j.val) by omega,pow_add]
    ring
  simp_rw [hp]
  have he : (∑ k : Fin (n+1), ∑ j : Fin (n+1), if k.val+j.val<2*n then X k*X j else 0)=
      (∑ k : Fin n, X k.castSucc)*(∑ j : Fin (n+1),X j)+
        X (Fin.last n)*(∑ j : Fin n, X j.castSucc) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact ite_eq_left (by simp only [Fin.val_castSucc]; omega)
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last]
      rw [ite_eq_right (by omega : ¬n+n<2*n),add_zero,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact ite_eq_left (by simp only [Fin.val_castSucc]; omega)
  rw [he]
  have ht : X (Fin.last n) ≤ ∑ j : Fin (n+1), X j := Finset.single_le_sum (fun j _ => hX j) (Finset.mem_univ _)
  have hl : 0 ≤ ∑ j : Fin n, X j.castSucc := Finset.sum_nonneg fun j _ => hX _
  have hfull : parameterNorm q BoundedMultiplier.one u=∑j : Fin (n+1),X j := by
    simp only [parameterNorm,BoundedMultiplier.one_seminorm,X]
  have hlow : lowerParameterNorm q u=∑j : Fin n,X j.castSucc := rfl
  rw [hfull,hlow]
  nlinarith [mul_le_mul_of_nonneg_right ht hl]

theorem boundedLipschitz_lowerOrderQuadratic_small (hS : IsBoundedLipschitzDomain S F)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      ∀ u : WeakSobolevJet d n (volume.restrict S) S,
      (∑ k : Fin (n+1), ∑ j : Fin (n+1), if k.val+j.val < 2*n then
        q^(2*n-k.val-j.val)*‖field k u‖*‖field j u‖ else 0) ≤
        η*‖u‖^2+C*q^(2*n)*‖value u‖^2 := by
  obtain ⟨C,hC,hbound⟩ := boundedLipschitz_lowerParameter_product_small hS n (half_pos hη)
  refine ⟨2*C,by linarith,?_⟩
  intro q hq u
  have he := hbound q hq u
  have hp : (q^n*‖value u‖)^2=q^(2*n)*‖value u‖^2 := by rw [mul_pow,←pow_mul,Nat.mul_comm n 2]
  rw [hp] at he
  exact (lowerOrderQuadratic_le (zero_le_one.trans hq) u).trans (by nlinarith [he])

end Carleman.WeakSobolevJet
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

theorem SobolevHilbert.toJet_norm_le (u : SobolevHilbert d n ν S) :
    ‖SobolevHilbert.toJet u‖ ≤ ‖u‖ := by
  change ‖(SobolevHilbert.toJet u : JetFields d n ν)‖ ≤ ‖u‖
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro k
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SobolevHilbert.norm_sq]
  exact Finset.single_le_sum (f := fun j : Fin (n+1) => ‖WeakSobolevJet.field j (SobolevHilbert.toJet u)‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem boundedLipschitz_hilbert_lowerOrderQuadratic_small (hS : IsBoundedLipschitzDomain S F)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      ∀ u : SobolevHilbert d n (volume.restrict S) S,
      (∑ k : Fin (n+1), ∑ j : Fin (n+1), if k.val+j.val < 2*n then
        q^(2*n-k.val-j.val)*‖WeakSobolevJet.field k (SobolevHilbert.toJet u)‖*
          ‖WeakSobolevJet.field j (SobolevHilbert.toJet u)‖ else 0) ≤
        η*‖u‖^2+C*q^(2*n)*‖SobolevHilbert.value u‖^2 := by
  obtain ⟨C,hC,hbound⟩ := WeakSobolevJet.boundedLipschitz_lowerOrderQuadratic_small hS n hη
  refine ⟨C,hC,?_⟩
  intro q hq u
  apply (hbound q hq (SobolevHilbert.toJet u)).trans
  exact add_le_add (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (SobolevHilbert.toJet_norm_le u)) hη.le) le_rfl
end Carleman
