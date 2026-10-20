module
public import Carleman.Spatial.UniformInnerHeat
public import Carleman.Spatial.BoxIntervalC2HeatEstimate
/-! Actual inner-domain estimates with constants chosen on the fixed outer domain. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem halfspaceSmoothInner_uniform_C2_heat_both_signs {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ kidx : ℕ, c ∈ halfspaceSmoothInner ℓ b kidx → ∀ T : ℝ, 0 < T → ∀ q : ℝ → ℝ, ContDiff ℝ 2 q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b kidx), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat ε u tx)^2)+
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hsmooth⟩ :=
    halfspaceSmoothInner_uniform_heat_both_signs ℓ b hbounded hW hne hWS
  refine ⟨c,l,β/9,qc,C,hc,hl,by positivity,by linarith,hqc,hC,hρ,?_⟩
  intro kidx hck T hT q hq hqp hqmin hq' hq'' ε hε u hu hup hub
  have hdomain := (halfspaceSmoothInner_compact ℓ b hbounded kidx).isBounded.subset subset_closure
  have hS := (halfspaceSmoothInner_open ℓ b kidx).measurableSet
  obtain ⟨B,_hB,qs,hqs,ht⟩ := exists_periodic_C2_smooth_qclass_exact hq hT hqp
    (by linarith) hβ.le hqmin hq' hq''
  have hseq (n : ℕ) := hsmooth kidx hck T hT.le (qs n) (hqs n).1 (hqs n).2.1
    (fun t _ => ((hqs n).2.2 t).1)
    (fun t _ => ((hqs n).2.2 t).2.2.1)
    (fun t _ => ((hqs n).2.2 t).2.2.2) ε hε u hu hup hub
  have hcont (n : ℕ) : Continuous (qs n) := (hqs n).1.continuous
  have hb (n : ℕ) (t : ℝ) : qs n t ∈ Icc 0 B :=
    ⟨(by linarith [((hqs n).2.2 t).1]),((hqs n).2.2 t).2.1⟩
  have hprofile : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates d) =>
      Real.exp (p.1*interiorCarlemanProfile c l p.2.2)) :=
    Real.continuous_exp.comp
      (continuous_fst.mul ((interiorCarlemanProfile_contDiff c l).continuous.comp continuous_snd.snd))
  have hgrad : Continuous (fun tx : ℝ × SpatialCoordinates d =>
      ‖gradient (fun y => u (tx.1,y)) tx.2‖^2) := by
    have he : (fun tx : ℝ × SpatialCoordinates d => ‖gradient (fun y => u (tx.1,y)) tx.2‖^2)=
        directionalEnergy spaceTimeSpatialDirection u :=
      funext fun tx => (spaceTime_directionalEnergy_gradient hu tx.1 tx.2).symm
    rw [he]
    exact (directionalEnergy_contDiff _ hu).continuous
  have hheat : Continuous (spaceTimeOrientedHeat ε u) := by
    have he : spaceTimeOrientedHeat ε u=(fun tx => ε*smoothD (1,0) u tx-
        directionalLap spaceTimeSpatialDirection u tx) := by
      funext tx
      rw [spaceTime_timeD hu tx.1 tx.2,spaceTime_directionalLap hu tx.1 tx.2]
      rfl
    rw [he]
    exact (continuous_const.mul (smoothD_contDiff hu _).continuous).sub (directionalLap_contDiff _ hu).continuous
  have hF₀ : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates d) =>
      p.1^3*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*(u p.2)^2) :=
    ((continuous_fst.pow 3).mul (hprofile.pow 2)).mul ((hu.continuous.comp continuous_snd).pow 2)
  have hF₁ : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates d) =>
      p.1*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*
        ‖gradient (fun y => u (p.2.1,y)) p.2.2‖^2) :=
    (continuous_fst.mul (hprofile.pow 2)).mul (hgrad.comp continuous_snd)
  have hR : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates d) =>
      (Real.exp (p.1*interiorCarlemanProfile c l p.2.2)*spaceTimeOrientedHeat ε u p.2)^2) :=
    (hprofile.mul (hheat.comp continuous_snd)).pow 2
  have ht₀ := domainTimeIntegral_tendsto_parameter _ hS hdomain T hcont hb ht hF₀
  have ht₁ := domainTimeIntegral_tendsto_parameter _ hS hdomain T hcont hb ht hF₁
  have htR := domainTimeIntegral_tendsto_parameter _ hS hdomain T hcont hb ht hR
  have htO := domainTimeIntegral_observation_tendsto_parameter _ hS hdomain T hW.measurableSet hcont hb ht hF₀
  exact le_of_tendsto_of_tendsto (ht₀.add ht₁) ((htR.add htO).const_mul C)
    (Filter.Eventually.of_forall hseq)

theorem halfspaceSmoothInner_uniform_interval_C2_heat_both_signs {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ kidx : ℕ, c ∈ halfspaceSmoothInner ℓ b kidx → ∀ T : ℝ, 0 < T → ∀ q : ℝ → ℝ, ContDiffOn ℝ 2 q (Icc 0 T) →
      q 0=q T → derivWithin q (Icc 0 T) 0=derivWithin q (Icc 0 T) T →
      derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) 0=
        derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |derivWithin q (Icc 0 T) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      ∀ u : (ℝ × SpatialCoordinates d) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (halfspaceSmoothInner ℓ b kidx), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat ε u tx)^2)+
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hglobal⟩ :=
    halfspaceSmoothInner_uniform_C2_heat_both_signs ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro kidx hck T hT q hq he0 he1 he2 hqmin hq' hq'' ε hε u hu hup hub
  obtain ⟨Q,hQ,hQp,hQe⟩ := exists_periodic_C2_extension hT hq he0 he1 he2
  have hfinal := hglobal kidx hck T hT Q hQ hQp
    (fun t ht => by rw [(hQe t ht).1]; exact hqmin t ht)
    (fun t ht => by rw [(hQe t ht).2.1,(hQe t ht).1]; exact hq' t ht)
    (fun t ht => by rw [(hQe t ht).2.2,(hQe t ht).1]; exact hq'' t ht) ε hε u hu hup hub
  have hI (F : ℝ × (ℝ × SpatialCoordinates d) → ℝ) :
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F (Q tx.1,tx))=
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F (q tx.1,tx)) := by
    apply domainTimeIntegral_congr_on _ (halfspaceSmoothInner_open ℓ b kidx).measurableSet
    intro t ht x _
    rw [(hQe t ht).1]
  have hO (F : ℝ × (ℝ × SpatialCoordinates d) → ℝ) :
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator (fun tx => F (Q tx.1,tx)))=
        domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator (fun tx => F (q tx.1,tx))) := by
    apply domainTimeIntegral_congr_on _ (halfspaceSmoothInner_open ℓ b kidx).measurableSet
    intro t ht x _
    by_cases hx : (t,x) ∈ Prod.snd ⁻¹' W
    · simp only [indicator_of_mem hx,(hQe t ht).1]
    · simp only [indicator_of_notMem hx]
  let F₀ := fun p : ℝ × (ℝ × SpatialCoordinates d) =>
    p.1^3*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*(u p.2)^2
  let F₁ := fun p : ℝ × (ℝ × SpatialCoordinates d) =>
    p.1*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*‖gradient (fun y => u (p.2.1,y)) p.2.2‖^2
  let R := fun p : ℝ × (ℝ × SpatialCoordinates d) =>
    (Real.exp (p.1*interiorCarlemanProfile c l p.2.2)*spaceTimeOrientedHeat ε u p.2)^2
  change domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F₀ (Q tx.1,tx))+
    domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => F₁ (Q tx.1,tx)) ≤
    C*(domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T (fun tx => R (Q tx.1,tx))+
      domainTimeIntegral (halfspaceSmoothInner ℓ b kidx) T ((Prod.snd ⁻¹' W).indicator (fun tx => F₀ (Q tx.1,tx)))) at hfinal
  rw [hI F₀,hI F₁,hI R,hO F₀] at hfinal
  exact hfinal

end Carleman
