module

public import Carleman.Section4.EnergyRate
public import Carleman.Section3.Statements

/-! The full energy-error and reconstructed-state conclusions with the
actual source norm. This layer composes N3 and Cea with Section 3's proved
Euler estimate, on the original associated operator and all solutions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X)
  (g : TimeGrid) (s : Orientation) (ρ : SpatialProfile ν) (w : TimeWeight)
  (L τ aE ηA K : ℝ)

/-- The energy half of Lemma 4.1, together with its reconstructed-state
stability conclusion. This is an output proposition, not numerical data. -/
def EnergyEstimate : Prop :=
  ∀ (f : g.Sequence (Lp ℝ 2 ν)) (u : g.Sequence a.model.domain) (z : g.Sequence X),
    a.model.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f →
    (∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*m) • r.G (z i) = r.J (f i)) →
    energyNorm hS hν a.sobolev g ρ w τ (fun i => Submodule.inclusion a.domain_le (u i)-r.R (z i)) ≤
      K*(aE+ηA)*g.l2Norm (ρ.nodeMap g w τ f) ∧
    energyNorm hS hν a.sobolev g ρ w τ (fun i => r.R (z i)) ≤ K*g.l2Norm (ρ.nodeMap g w τ f)

variable (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)

/-- The graph conclusion supplies the source norm; no final error bound
is assumed. A common constant serves error and state stability. -/
theorem energy_estimate_of_cea {aE a0 ηA Kc Cf Kg : ℝ}
    (haE : 0 ≤ aE) (haE1 : aE ≤ 1) (hη : 0 ≤ ηA) (hη1 : ηA ≤ 1)
    (hKc : 0 ≤ Kc) (hCf : 0 ≤ Cf)
    (ha : WeightedApproximation hS hν a.sobolev hD a.domain_le r g ρ w τ aE a0)
    (heuler : Section3.EulerEstimate hS hν a.model hD g s w ρ L τ Kg)
    (hcea : ∀ (f : g.Sequence (Lp ℝ 2 ν)) (u : g.Sequence a.model.domain) (z : g.Sequence X),
      a.model.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f →
      (∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*m) • r.G (z i) = r.J (f i)) →
      energyNorm hS hν a.sobolev g ρ w τ (fun i => r.R (z i-r.J (u i : Lp ℝ 2 ν))) ≤
        Kc*(Cf*energyNorm hS hν a.sobolev g ρ w τ
          (fun i => Submodule.inclusion a.domain_le (u i)-r.Q (u i : Lp ℝ 2 ν))+
          ηA*energyNorm hS hν a.sobolev g ρ w τ (fun i => r.Q (u i : Lp ℝ 2 ν)))) :
    EnergyEstimate a r A g s ρ w L τ aE ηA (((m+2)+Kc*(Cf+(m+2)))*Kg) := by
  intro f u z hu hz
  obtain ⟨herr,hstate⟩ := energy_rates_of_cea hS hν a.sobolev hD a.domain_le r g ρ w τ
    haE haE1 hη hη1 hKc hCf ha u z (hcea f u z hu hz)
  have hreg : regularityNorm hS hν hD g ρ w τ u ≤ Kg*g.l2Norm (ρ.nodeMap g w τ f) := by
    have he := (heuler f).2 u hu
    have hn := g.l2Norm_nonneg (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν))))
    linarith only [he,hn]
  have hn := regularityNorm_nonneg hS hν hD g ρ w τ u
  have hC : 0 ≤ ((m+2:ℝ)+Kc*(Cf+(m+2))) := by positivity
  have hc : 1+Kc*(Cf+(m+2)) ≤ (m+2:ℝ)+Kc*(Cf+(m+2)) := by linarith [Nat.cast_nonneg (α := ℝ) m]
  constructor
  · have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (add_nonneg haE hη)) hn
    have hb := mul_le_mul_of_nonneg_left hreg (mul_nonneg hC (add_nonneg haE hη))
    exact herr.trans (he.trans (hb.trans_eq (by ring)))
  · exact hstate.trans ((mul_le_mul_of_nonneg_left hreg hC).trans_eq (by ring))

end Carleman.Section4
