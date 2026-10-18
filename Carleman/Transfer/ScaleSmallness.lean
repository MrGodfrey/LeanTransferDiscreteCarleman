module

public import Carleman.Transfer.ScaleBudgets

/-! Uniform sufficient scales for every smallness condition of Theorem 2.1.
Zero energy-budget exponent terms are controlled by h0 and Delta0. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
namespace Carleman

theorem exists_scale_smallness (a : CarlemanExponents) (C δx δt ηstar cStar : ℝ)
    (hC : 0 ≤ C) (hδx : 0 < δx) (hδt : 0 < δt) (hη : 0 < ηstar) (hc : 0 < cStar) :
    ∃ κ h0 Δ0 : ℝ, 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧
      ∀ (g : TimeGrid) (h Q : ℝ) (errors : ErrorScales), 0 < h → h ≤ h0 → g.dt ≤ Δ0 →
      1 ≤ Q → Q ≤ κ*min (h^(-a.alphaX)) (g.dt^(-a.alphaT)) →
      errors.aE ≤ C*h^a.m → errors.a₀+errors.ηA ≤ C*h^(2*a.m) →
      errors.aE ≤ 1 ∧ errors.ηA ≤ ηstar ∧ h*Q ≤ δx ∧ g.dt*Q^2 ≤ δt ∧
      errors.loadDefect g a Q ≤ 1 ∧ errors.stateDefect g a Q ≤ cStar := by
  let M := ErrorScales.approximationConstant C
  have hM : 0 < M := ErrorScales.approximationConstant_pos C
  let ε := min 1 cStar/(4*M)
  have hε : 0 < ε := div_pos (lt_min zero_lt_one hc) (by positivity)
  obtain ⟨κE,hκE,hκE1,hκEbound⟩ : ∃ κE : ℝ, 0 < κE ∧ κE ≤ 1 ∧
      (a.nuEnergy = 0 ∨ ∀ x : ℝ, 0 ≤ x → x ≤ κE → x^a.nuEnergy ≤ ε) := by
    by_cases hz : a.nuEnergy = 0
    · exact ⟨1,zero_lt_one,le_rfl,Or.inl hz⟩
    · obtain ⟨k,hk,hk1,hkb⟩ := exists_small_rpow
        (lt_of_le_of_ne a.nuEnergy_nonneg (Ne.symm hz)) hε
      exact ⟨k,hk,hk1,Or.inr hkb⟩
  obtain ⟨κ0,hκ0,hκ01,hκ0bound⟩ := exists_small_rpow a.nuL2_pos hε
  let κ := min δx (min (Real.sqrt δt) (min κE κ0))
  have hκ : 0 < κ := lt_min hδx (lt_min (Real.sqrt_pos.mpr hδt) (lt_min hκE hκ0))
  have hκx : κ ≤ δx := min_le_left _ _
  have hκt : κ ≤ Real.sqrt δt := (min_le_right _ _).trans (min_le_left _ _)
  have hκe : κ ≤ κE := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκz : κ ≤ κ0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hκt2 : κ^2 ≤ δt := by
    have hh := (sq_le_sq₀ hκ.le (Real.sqrt_nonneg _)).mpr hκt
    simpa only [Real.sq_sqrt hδt.le] using hh
  let r := min ε (min (1/(C+1)) (ηstar/(C+1)))
  have hr : 0 < r := lt_min hε (lt_min (by positivity) (by positivity))
  obtain ⟨h0,hh0,hh01,hhbound⟩ := exists_small_rpow
    (Nat.cast_pos.mpr a.m_pos : (0:ℝ) < a.m) hr
  refine ⟨κ,h0,min 1 ε,hκ,hh0,hh01,lt_min zero_lt_one hε,min_le_left _ _,?_⟩
  intro g h Q errors hh hh0' hdt hQ hscale hE h0err
  have hh1 := hh0'.trans hh01
  have hdt1 := hdt.trans (min_le_left _ _)
  have hdtε := hdt.trans (min_le_right _ _)
  have hQ0 := zero_le_one.trans hQ
  have hp : h^a.m ≤ r := by simpa only [Real.rpow_natCast] using hhbound h hh.le hh0'
  have hp0 : 0 ≤ h^a.m := pow_nonneg hh.le _
  have hp1 : h^a.m ≤ 1 := pow_le_one₀ hh.le hh1
  have hp2 : h^(2*a.m) = (h^a.m)^2 := by rw [← pow_mul]; congr 1; omega
  have hp21 : h^(2*a.m) ≤ h^a.m := by rw [hp2]; nlinarith
  have hCE1 : (C+1)*h^a.m ≤ 1 := by
    have hh := hp.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < C+1)).mp hh
    nlinarith only [hh']
  have hCEη : (C+1)*h^a.m ≤ ηstar := by
    have hh := hp.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < C+1)).mp hh
    nlinarith only [hh']
  have hηbound : errors.ηA ≤ C*h^a.m :=
    ((le_add_of_nonneg_left errors.a₀_nonneg).trans h0err).trans
      (mul_le_mul_of_nonneg_left hp21 hC)
  have hscaleX : Q ≤ κ*h^(-a.alphaX) := hscale.trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hκ.le)
  have hscaleT : Q ≤ κ*g.dt^(-a.alphaT) := hscale.trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hκ.le)
  have hB := a.scale_bounds
  have hxQ : h*Q ≤ κ := by
    simpa using scale_monomial_le (p := (1:ℝ)) hh hh1 hQ0 hκ.le (by norm_num : (0:ℝ) ≤ 1)
      (by simpa only [mul_one] using hB.2.1) hscaleX
  have htQ : g.dt*Q^2 ≤ κ^2 := by
    simpa only [Real.rpow_one,Real.rpow_two] using scale_monomial_le g.dt_pos hdt1 hQ0 hκ.le
      (by norm_num : (0:ℝ) ≤ 2) (show a.alphaT*2 ≤ 1 by linarith [hB.2.2.2.1]) hscaleT
  have hsE : h^(2*a.m)*Q^a.nuEnergy ≤ ε := by
    rcases hκEbound with hz | hk
    · simpa only [hz,Real.rpow_zero,mul_one] using hp21.trans (hp.trans (min_le_left _ _))
    · have hs := scale_monomial_le hh hh1 hQ0 hκ.le a.nuEnergy_nonneg
        (show a.alphaX*a.nuEnergy ≤ ((2*a.m:ℕ):ℝ) by exact_mod_cast hB.2.2.2.2.1) hscaleX
      have hs' : h^(2*a.m)*Q^a.nuEnergy ≤ κ^a.nuEnergy := by simpa only [Real.rpow_natCast] using hs
      exact hs'.trans (hk κ hκ.le hκe)
  have htE : g.dt*Q^a.nuEnergy ≤ ε := by
    rcases hκEbound with hz | hk
    · simpa only [hz,Real.rpow_zero,mul_one] using hdtε
    · have hs := scale_monomial_le g.dt_pos hdt1 hQ0 hκ.le a.nuEnergy_nonneg
        hB.2.2.2.2.2.2.1 hscaleT
      have hs' : g.dt*Q^a.nuEnergy ≤ κ^a.nuEnergy := by simpa only [Real.rpow_one] using hs
      exact hs'.trans (hk κ hκ.le hκe)
  have hs0 : h^(4*a.m)*Q^a.nuL2 ≤ ε := by
    have hs := scale_monomial_le hh hh1 hQ0 hκ.le a.nuL2_pos.le
      (show a.alphaX*a.nuL2 ≤ ((4*a.m:ℕ):ℝ) by exact_mod_cast hB.2.2.2.2.2.1) hscaleX
    have hs' : h^(4*a.m)*Q^a.nuL2 ≤ κ^a.nuL2 := by simpa only [Real.rpow_natCast] using hs
    exact hs'.trans (hκ0bound κ hκ.le hκz)
  have ht0 : g.dt^2*Q^a.nuL2 ≤ ε := by
    have hs := scale_monomial_le g.dt_pos hdt1 hQ0 hκ.le a.nuL2_pos.le
      hB.2.2.2.2.2.2.2 hscaleT
    have hs' : g.dt^2*Q^a.nuL2 ≤ κ^a.nuL2 := by simpa only [Real.rpow_two] using hs
    exact hs'.trans (hκ0bound κ hκ.le hκz)
  have rates := errors.approximation_rates g a.m C h hC hh.le hh1 hE h0err
  have hsum : (errors.energy g)^2*Q^a.nuEnergy+(errors.l2 g)^2*Q^a.nuL2 ≤ min 1 cStar := by
    have h1 := mul_le_mul_of_nonneg_right rates.1 (Real.rpow_nonneg hQ0 a.nuEnergy)
    have h2 := mul_le_mul_of_nonneg_right rates.2 (Real.rpow_nonneg hQ0 a.nuL2)
    have hb : M*((h^(2*a.m)+g.dt)*Q^a.nuEnergy+(h^(4*a.m)+g.dt^2)*Q^a.nuL2) ≤ M*(4*ε) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hsE,htE,hs0,ht0]) hM.le
    have he : M*(4*ε) = min 1 cStar := by dsimp [ε]; field_simp
    rw [he] at hb
    nlinarith only [h1,h2,hb]
  have defects := errors.defects_le_budget g a Q hQ
  refine ⟨by nlinarith only [hE,hCE1,hp0],by nlinarith only [hηbound,hCEη,hp0],
    hxQ.trans hκx,htQ.trans hκt2,?_,?_⟩
  · exact defects.1.trans (hsum.trans (min_le_left _ _))
  · exact defects.2.trans (hsum.trans (min_le_right _ _))

end Carleman
