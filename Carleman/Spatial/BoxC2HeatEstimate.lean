module

public import Carleman.Spatial.BoxSmoothHeatBothSigns
public import Carleman.Spatial.BoxTimeIntegralLimit
public import Carleman.Weights.PeriodicC2Mollification

/-! The actual two-sign box estimate with global C² periodic weights and smooth states. -/
@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem box_C2_gaussian_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ T : ℝ, 0 < T → ∀ q : ℝ → ℝ, ContDiff ℝ 2 q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      ∀ u : (ℝ × SpatialCoordinates (d+1)) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (openCoordinateBox a b), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      boxTimeIntegral a b T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      boxTimeIntegral a b T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(boxTimeIntegral a b T (fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat ε u tx)^2)+
        boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hsmooth⟩ :=
    box_smooth_gaussian_heat_both_signs a b hpos hW hne hWS
  refine ⟨c,l,β/9,qc,C,hc,hl,by positivity,by linarith,hqc,hC,hρ,?_⟩
  intro T hT q hq hqp hqmin hq' hq'' ε hε u hu hup hub
  obtain ⟨B,_hB,qs,hqs,ht⟩ := exists_periodic_C2_smooth_qclass_exact hq hT hqp
    (by linarith) hβ.le hqmin hq' hq''
  have hseq (n : ℕ) := hsmooth T hT.le (qs n) (hqs n).1 (hqs n).2.1
    (fun t _ => ((hqs n).2.2 t).1)
    (fun t _ => ((hqs n).2.2 t).2.2.1)
    (fun t _ => ((hqs n).2.2 t).2.2.2) ε hε u hu hup hub
  have hcont (n : ℕ) : Continuous (qs n) := (hqs n).1.continuous
  have hb (n : ℕ) (t : ℝ) : qs n t ∈ Icc 0 B :=
    ⟨(by linarith [((hqs n).2.2 t).1]),((hqs n).2.2 t).2.1⟩
  have hprofile : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
      Real.exp (p.1*interiorCarlemanProfile c l p.2.2)) :=
    Real.continuous_exp.comp
      (continuous_fst.mul ((interiorCarlemanProfile_contDiff c l).continuous.comp continuous_snd.snd))
  have hgrad : Continuous (fun tx : ℝ × SpatialCoordinates (d+1) =>
      ‖gradient (fun y => u (tx.1,y)) tx.2‖^2) := by
    have he : (fun tx : ℝ × SpatialCoordinates (d+1) => ‖gradient (fun y => u (tx.1,y)) tx.2‖^2)=
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
  have hF₀ : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
      p.1^3*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*(u p.2)^2) :=
    ((continuous_fst.pow 3).mul (hprofile.pow 2)).mul ((hu.continuous.comp continuous_snd).pow 2)
  have hF₁ : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
      p.1*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*
        ‖gradient (fun y => u (p.2.1,y)) p.2.2‖^2) :=
    (continuous_fst.mul (hprofile.pow 2)).mul (hgrad.comp continuous_snd)
  have hR : Continuous (fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
      (Real.exp (p.1*interiorCarlemanProfile c l p.2.2)*spaceTimeOrientedHeat ε u p.2)^2) :=
    (hprofile.mul (hheat.comp continuous_snd)).pow 2
  have ht₀ := boxTimeIntegral_tendsto_parameter a b T hcont hb ht hF₀
  have ht₁ := boxTimeIntegral_tendsto_parameter a b T hcont hb ht hF₁
  have htR := boxTimeIntegral_tendsto_parameter a b T hcont hb ht hR
  have htO := boxTimeIntegral_observation_tendsto_parameter a b T hW.measurableSet hcont hb ht hF₀
  exact le_of_tendsto_of_tendsto (ht₀.add ht₁) ((htR.add htO).const_mul C)
    (Filter.Eventually.of_forall hseq)

end Carleman
