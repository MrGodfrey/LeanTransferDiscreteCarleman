module

public import Carleman.Section4.NodalApproximation

/-! Exactly N3 on the original domain and the actual weighted Sobolev/L²
norms. Its nodal consequences are proved, never included as data fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d (2*m) ν S) (hDV : D ≤ V)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction V X) (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

abbrev energyNorm (v : g.Sequence V) : ℝ :=
  g.weightedNorm (energySeminorm hS hν hV g ρ w τ) v

abbrev regularityNorm (u : g.Sequence D) : ℝ :=
  WeakSobolevJet.nodeParameterNorm g (w.nodes g) (fun i => ρ.multiplier w τ (g.nodeTime i))
    (fun i => domainSobolevJet hS hν hD (u i))

/-- N3, at every actual time in the original closed period. -/
structure WeightedApproximation (aE a0 : ℝ) : Prop where
  energy : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t)
      (Submodule.inclusion hDV v-r.Q (v : Lp ℝ 2 ν)) ≤
      aE*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v
  l2 : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    (ρ.multiplier w τ t).seminorm ((v : Lp ℝ 2 ν)-r.RH (r.J (v : Lp ℝ 2 ν))) ≤
      a0*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v

/-- No N3 assumption is needed for the original state itself. -/
theorem nodal_energy_le_regularity (u : g.Sequence D) :
    energyNorm hS hν hV g ρ w τ (fun i => Submodule.inclusion hDV (u i)) ≤
      (m+1:ℝ)*regularityNorm hS hν hD g ρ w τ u := by
  apply WeakSobolevJet.nodal_approximation_bound g (w.nodes g) (fun i => w.nonneg _)
    (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i))
    (energySeminorm hS hν hV g ρ w τ) _ (by positivity)
  intro i
  rw [energySeminorm,conformingWeightedSeminorm_apply _ _ _ (w.nonneg _)]
  exact conforming_energy_le_parameterNorm hS hν hV hD hDV (by omega) (w.lower _) _ _

theorem WeightedApproximation.nodal_energy {aE a0 : ℝ}
    (ha : WeightedApproximation hS hν hV hD hDV r g ρ w τ aE a0)
    (haE : 0 ≤ aE) (u : g.Sequence D) :
    energyNorm hS hν hV g ρ w τ (fun i => Submodule.inclusion hDV (u i)-r.Q (u i : Lp ℝ 2 ν)) ≤
      aE*regularityNorm hS hν hD g ρ w τ u := by
  apply WeakSobolevJet.nodal_approximation_bound g (w.nodes g) (fun i => w.nonneg _)
    (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i))
    (energySeminorm hS hν hV g ρ w τ) _ haE
  intro i
  rw [energySeminorm,conformingWeightedSeminorm_apply _ _ _ (w.nonneg _)]
  exact ha.energy _ (g.cellTime_mem i.val (Nat.le_of_lt i.isLt)) (u i)

theorem WeightedApproximation.nodal_Q {aE a0 : ℝ}
    (ha : WeightedApproximation hS hν hV hD hDV r g ρ w τ aE a0)
    (haE : 0 ≤ aE) (u : g.Sequence D) :
    energyNorm hS hν hV g ρ w τ (fun i => r.Q (u i : Lp ℝ 2 ν)) ≤
      (m+1+aE:ℝ)*regularityNorm hS hν hD g ρ w τ u := by
  have he : (fun i => r.Q (u i : Lp ℝ 2 ν)) =
      (fun i => Submodule.inclusion hDV (u i))-
      (fun i => Submodule.inclusion hDV (u i)-r.Q (u i : Lp ℝ 2 ν)) := by
    funext i
    simp only [Pi.sub_apply,sub_sub_cancel]
  rw [energyNorm,he]
  exact (g.weightedNorm_sub_le _ _ _).trans
    ((add_le_add (nodal_energy_le_regularity hS hν hV hD hDV g ρ w τ u)
      (ha.nodal_energy hS hν hV hD hDV r g ρ w τ haE u)).trans_eq (by ring))

/-- The L² approximation uses the same actual spatial R graph and no
additional regularity of the trajectory between nodes. -/
theorem WeightedApproximation.nodal_l2 {aE a0 : ℝ}
    (ha : WeightedApproximation hS hν hV hD hDV r g ρ w τ aE a0)
    (ha0 : 0 ≤ a0) (u : g.Sequence D) :
    g.l2Norm (ρ.nodeMap g w τ (fun i => (u i : Lp ℝ 2 ν)-r.RH (r.J (u i : Lp ℝ 2 ν)))) ≤
      a0*regularityNorm hS hν hD g ρ w τ u := by
  have he := WeakSobolevJet.nodal_approximation_bound g (w.nodes g) (fun i => w.nonneg _)
    (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i))
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm)
    (fun i => (u i : Lp ℝ 2 ν)-r.RH (r.J (u i : Lp ℝ 2 ν))) ha0
    (fun i => ha.l2 _ (g.cellTime_mem i.val (Nat.le_of_lt i.isLt)) (u i))
  exact he

end Carleman.Section4
