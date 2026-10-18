module

public import Carleman.Section4.EnergyEstimate
public import Carleman.Section4.TestData
public import Carleman.Section3.Complete

/-! Uniform energy error from the original analytic and numerical data.
Every multiplication, form, time-margin, approximation, Cea and Euler bound
is supplied by its proved theorem; no spatial estimate is an input. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
universe u
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}

/-- One σ² multiplication constant serves both profile signs. -/
theorem squared_weight_signed_uniform (hbounded : Bornology.IsBounded S)
    {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
    (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ (w : TimeWeight) (τ t : ℝ) (e : Bool)
      (hw : ∀ v : V, ((ρ.signed e).multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V)
      (_hξ : ∀ v : V, ((ρ.signed e).neg.multiplier w (-τ) t).map (v : Lp ℝ 2 ν) ∈ V) (v : V),
      conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).neg.multiplier w (-τ) t)
        (conformingWeight ((ρ.signed e).multiplier w τ t) hw
          (conformingWeight ((ρ.signed e).multiplier w τ t) hw v)) ≤
      CM*conformingWeightedNorm hS hν hV (w.q t) ((ρ.signed e).multiplier w τ t) v := by
  obtain ⟨Cp,hCp,hp⟩ := squared_weight_test_uniform hS hbounded hν hV ρ hρ
  obtain ⟨Cn,hCn,hn⟩ := squared_weight_test_uniform hS hbounded hν hV ρ.neg hρ.neg
  refine ⟨max Cp Cn,hCp.trans_le (le_max_left _ _),?_⟩
  intro w τ t e hw hξ v
  cases e
  · exact (hp w τ t hw hξ v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (conformingWeightedNorm_nonneg _ _ _ _ _ _))
  · exact (hn w τ t hw hξ v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (conformingWeightedNorm_nonneg _ _ _ _ _ _))

/-- Collect the original cell and Euler time thresholds before selecting a
period, q, grid, orientation or state. -/
theorem spatial_time_threshold {β τStar R δ : ℝ}
    (hβ : 0 < β) (hτ : 0 ≤ τStar) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ δt : ℝ, 0 < δt ∧ δt ≤ δ ∧ ∀ t : ℝ, 0 ≤ t → t ≤ δt →
      β*t ≤ 1/2 ∧ (4*β*(τStar+R))*t ≤ 1 := by
  let M := 4*β*(τStar+R)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δt := min δ (min (1/(2*(β+1))) (1/(M+1)))
  refine ⟨δt,lt_min hδ (lt_min (by positivity) (by positivity)),min_le_left _ _,?_⟩
  intro t ht htd
  have ht₁ := htd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht₂ := htd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1 := (le_div_iff₀ (show 0 < 2*(β+1) by positivity)).mp ht₁
  have h2 := (le_div_iff₀ (show 0 < M+1 by positivity)).mp ht₂
  constructor <;> nlinarith only [h1,h2,ht]

variable (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  (ρ : SpatialProfile ν) (c C Ccomm β τStar Ctime Csuper δnum : ℝ)

/-- The energy half of original Lemma 4.1 with all varying numerical data
quantified after the constants. The full lemma also requires the L² rate. -/
def EnergyUniform : Prop :=
  ∃ Lmin δt : ℝ, 1 ≤ Lmin ∧ 0 < δt ∧ ∀ L : ℝ, Lmin ≤ L →
    ∃ δx ηstar K : ℝ, 0 < δx ∧ δx ≤ δnum ∧ 0 < ηstar ∧ 0 < K ∧
      ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ),
      (∀ z v, inner ℝ (A z) v = a.scalarForm (r.R z) (r.R v)+b z v) →
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight), TimeWeightRegularity w g β →
      g.dt*w.max^2 ≤ δt → ∀ (τ : ℝ) (e : Bool), |τ| ≤ τStar →
      Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar →
      ∀ (mesh aE a0 ηA : ℝ), 0 ≤ mesh → mesh*w.max ≤ δx →
      0 ≤ aE → aE ≤ 1 → 0 ≤ ηA → ηA ≤ ηstar →
      WeightedApproximation hS hν a.sobolev hD a.domain_le r g (ρ.signed e) w τ aE a0 →
      WeightedTest hS hν a.sobolev r g (ρ.signed e) w τ Ctime Csuper mesh →
      (∀ i z v, |b z v| ≤
        ηA*conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
          ((ρ.signed e).multiplier w τ (g.nodeTime i)) (r.R z)*
        conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
          ((ρ.signed e).neg.multiplier w (-τ) (g.nodeTime i)) (r.R v)) →
      EnergyEstimate a r A g s (ρ.signed e) w L τ aE ηA K

/-- Section 3 is used as a proved dependency, not replaced by a new bridge
assumption; the original A1 wrapper below supplies it internally. -/
theorem energy_uniform_of_section3 (hbounded : Bornology.IsBounded S)
    (hρ : SmoothOnClosure ρ.value S) (hc : 0 < c) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    {Kg δ : ℝ} {L₀ : ℝ → ℝ} (hKg : 0 < Kg) (hδ : 0 < δ)
    (H : Section3.Conclusions hS hν a.model a.sobolev a.domain_le hD a.scalarForm
      ρ c C Ccomm β τStar Kg L₀ δ) :
    EnergyUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨CM,hCM,hM⟩ := squared_weight_signed_uniform (hS := hS) (hν := hν) hbounded a.sobolev ρ hρ
  obtain ⟨δt,hδt,hδtδ,ht⟩ := spatial_time_threshold hβ hτ ρ.bound_nonneg hδ
  let B := 18*Ctime+1
  have hB : 0 < B := by dsimp [B]; positivity
  let Lmin := max (L₀ 1) (L₀ B)
  refine ⟨Lmin,δt,(H.threshold 1 zero_lt_one).trans (le_max_left _ _),hδt,?_⟩
  intro L hL
  have hL1 : 1 ≤ L := (H.threshold 1 zero_lt_one).trans ((le_max_left _ _).trans hL)
  obtain ⟨Cf,hCf,hform⟩ := H.form_bound L hL1
  obtain ⟨δx,ηstar,hδx,hδxnum,hηstar,hηstar1,hsmall⟩ :=
    spatial_smallness_thresholds hc hCf.le hCM.le hCs hδnum
  let Kc := (2/c)*(1+CM)
  have hKc : 0 < Kc := by dsimp [Kc]; positivity
  let K := ((m+2:ℝ)+Kc*(Cf+(m+2)))*Kg
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨δx,ηstar,K,hδx,hδxnum,hηstar,hK,?_⟩
  intro X _ _ r A b hA g s w hw hmesh τ e hτw ha mesh aE a0 ηA hmesh0 hx haE haE1 hη hηs happ T hdef
  have hη1 : ηA ≤ 1 := hηs.trans hηstar1
  have htime := ht (g.dt*w.max^2) (mul_nonneg g.dt_pos.le (sq_nonneg _)) hmesh
  have hr : (ρ.signed e).bound = ρ.bound := by cases e <;> rfl
  have htime1 : β*g.dt*w.max^2 ≤ 1/2 := by nlinarith only [htime.1]
  have htime2 : (4*β*(τStar+(ρ.signed e).bound))*g.dt*w.max^2 ≤ 1 := by
    rw [hr]
    nlinarith only [htime.2]
  have hs := hsmall (mesh*w.max) ηA (mul_nonneg hmesh0 (zero_le_one.trans w.max_ge_one)) hx hη hηs
  let ε := Csuper*mesh*w.max
  have hε : 0 ≤ ε := by dsimp [ε]; positivity [w.max_ge_one]
  have hε1 : ε ≤ 1 := by simpa only [ε,mul_assoc] using hs.1
  have hs' : Cf*ε+ηA*(ε+CM) ≤ c/2 := by simpa only [ε,mul_assoc] using hs.2
  apply energy_estimate_of_cea a r A g s (ρ.signed e) w L τ hD
    haE haE1 hη hη1 hKc.le hCf.le happ
    (H.euler g s w hw L τ e ((le_max_left _ _).trans hL) (hmesh.trans hδtδ) hτw ha)
  intro f u z hu hz
  let uV : g.Sequence a.V := fun i => Submodule.inclusion a.domain_le (u i)
  let μ : g.Sequence ℝ := fun i => (L*w.nodes g i)^(2*m)
  let hp := (ha.data e τ hτw).form_preserving
  have huV : ∀ (i : g.Index) (v : a.V),
      inner ℝ (s.difference g (fun j => (uV j : Lp ℝ 2 ν)) i) (v : Lp ℝ 2 ν)+
        Reconstruction.spatialForm a.bilinearForm (μ i) (uV i) v = inner ℝ (f i) (v : Lp ℝ 2 ν) := by
    intro i v
    exact Reconstruction.spatial_continuous_test g s a.domain_le a.model.operator a.bilinearForm
      (fun u v => (a.operator_test u v).symm) μ f u (fun i => congrFun hu i) i v
  have hnode (i : g.Index) : g.nodeTime i ∈ Icc 0 g.period :=
    g.cellTime_mem i.val (Nat.le_of_lt i.isLt)
  have hraw := spatial_cea hS hν a.sobolev r g s (ρ.signed e) w β τ τStar hw hτw htime1 htime2
    a.bilinearForm A b hA μ T.op T.derivative T.endpoint T.hasDeriv
    (fun i => T.symmetric _ (hnode i)) (fun i => T.nonneg _ (hnode i)) hp
    hc hCf.le hCt hCM.le hε hη T.time_bound
    (fun i v z => hform w τ e hτw ha _ v z)
    (by
      intro i v
      have hh := H.form_coercive B hB L ((le_max_right _ _).trans hL) w τ e hτw ha (g.nodeTime i) v
      have hn := sq_nonneg (w.q (g.nodeTime i)*((ρ.signed e).multiplier w τ (g.nodeTime i)).seminorm (v : Lp ℝ 2 ν))
      change c*(conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
        ((ρ.signed e).multiplier w τ (g.nodeTime i)) v)^2+(18*Ctime)*_ ≤ _
      change c*(conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
        ((ρ.signed e).multiplier w τ (g.nodeTime i)) v)^2+B*_ ≤ _ at hh
      dsimp only [B] at hh
      simp only [Reconstruction.spatialForm,OriginalForm.bilinearForm_apply,shiftedForm,μ,TimeWeight.nodes] at hh ⊢
      linarith only [hh,hn]) hdef
    (fun i v => hM w τ _ e (hp _) ((ha.inverse hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar e τ hτw).form_preserving _) v)
    (fun i z => T.superapprox _ (hnode i) (hp _) z) hs' f uV z huV hz
  have hcoeff : (2/c)*(ε+CM) ≤ Kc := mul_le_mul_of_nonneg_left (add_le_add hε1 le_rfl) (by positivity)
  have hn : 0 ≤ Cf*energyNorm hS hν a.sobolev g (ρ.signed e) w τ
      (fun i => uV i-r.Q (u i : Lp ℝ 2 ν))+
      ηA*energyNorm hS hν a.sobolev g (ρ.signed e) w τ (fun i => r.Q (u i : Lp ℝ 2 ν)) :=
    add_nonneg (mul_nonneg hCf.le (g.weightedNorm_nonneg _ _))
      (mul_nonneg hη (g.weightedNorm_nonneg _ _))
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hn)

end Carleman.Section4

namespace Carleman.OriginalForm
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  (a : OriginalForm (m := m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ in
/-- The energy error and state estimate of Lemma 4.1 from the original analytic
assumptions and N3/N4. Section 3 and every absorption threshold are internal. -/
theorem spatial_energy_uniform (hm : 0 < m) (Creg c C Ccomm β τStar Ctime Csuper δnum : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section4.EnergyUniform a hD ρ c C Ccomm β τStar Ctime Csuper δnum := by
  obtain ⟨Kg,hKg,L₀,δ,hδ,_,H⟩ := a.section3 hΩ hD ρ hρ
    hm Creg c C Ccomm β τStar hc hC hCcomm hβ hτStar hell
  exact Section4.energy_uniform_of_section3 a hD ρ c C Ccomm β τStar Ctime Csuper δnum
    hΩ.isBounded hρ hc hβ hτStar hCt hCs hδnum hKg hδ H

end Carleman.OriginalForm
