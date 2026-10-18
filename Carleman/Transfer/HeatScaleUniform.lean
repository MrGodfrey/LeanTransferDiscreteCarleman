module

public import Carleman.Transfer.ScaleUniform

/-! The full heat-exponent specialization of the original scale corollary. -/
@[expose] public noncomputable section
open MeasureTheory Set
universe u v y
namespace Carleman.OriginalForm
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hΩ : IsBoundedLipschitzDomain S E)
  (a : OriginalForm (m := CarlemanExponents.heat.m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*CarlemanExponents.heat.m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
  {Z : Fin CarlemanExponents.heat.m → Type*} [∀ j, NormedAddCommGroup (Z j)] [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin CarlemanExponents.heat.m, DifferentialExpression (volume.restrict S)
      (fun k : Fin (CarlemanExponents.heat.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)

include hρ in
/-- Corollary 2.3 from the original assumptions and approximation orders.
Both load and right-inverse residual estimates hold for every state. -/
theorem heat_scale_uniform (Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce : ℝ)
    (hCap : 0 ≤ Cap) (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (CarlemanExponents.heat.dStar/2) (CarlemanExponents.heat.bStar/2) ≤ τStar)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section5.ScaleUniform.{u,v,y} (α := CarlemanExponents.heat) a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper Cnum Cce Cap (4/5) (2/5) := by
  have hh := a.scale_uniform hΩ hD ρ hρ P obs hobs Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce
    hCap hc hC hCc hβ hτ hCt hCs hδ hCn hCce hcover hell
  simpa only [CarlemanExponents.heat_scale_exponents.2.2.2.2.1,
    CarlemanExponents.heat_scale_exponents.2.2.2.2.2] using hh

end Carleman.OriginalForm
