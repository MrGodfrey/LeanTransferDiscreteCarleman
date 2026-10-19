module

public import Carleman.Spatial.PhysicalFiniteSpace
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Continuous diagonal families on the actual finite physical Hilbert space. -/
@[expose] public noncomputable section
open Set
namespace Carleman.PhysicalFiniteSpace
variable {ι : Type*} [Fintype ι] {mass : ℝ} {hmass : 0 < mass}

def multiplierFamily : (ι → ℝ) →L[ℝ]
    (PhysicalFiniteSpace ι mass hmass →L[ℝ] PhysicalFiniteSpace ι mass hmass) :=
  LinearMap.toContinuousLinearMap {
    toFun := multiplier
    map_add' := by
      intro b c
      apply ContinuousLinearMap.ext
      intro f
      apply valuesEquiv.injective
      funext i
      change (b i+c i)*f i=b i*f i+c i*f i
      ring
    map_smul' := by
      intro c b
      apply ContinuousLinearMap.ext
      intro f
      apply valuesEquiv.injective
      funext i
      change (c*b i)*f i=c*(b i*f i)
      ring }

theorem multiplierFamily_apply (b : ι → ℝ) (f : PhysicalFiniteSpace ι mass hmass) (i : ι) :
    multiplierFamily b f i=b i*f i := rfl

theorem multiplierFamily_hasDerivWithinAt (b : ℝ → ι → ℝ) (b' : ι → ℝ)
    (S : Set ℝ) (t : ℝ)
    (hb : ∀ i, HasDerivWithinAt (fun s => b s i) (b' i) S t) :
    HasDerivWithinAt (fun s => multiplierFamily (hmass := hmass) (b s))
      (multiplierFamily b') S t := by
  let L : (ι → ℝ) →L[ℝ]
      (PhysicalFiniteSpace ι mass hmass →L[ℝ] PhysicalFiniteSpace ι mass hmass) := multiplierFamily
  have hL : HasFDerivAt L L (b t) := L.hasFDerivAt
  have hb' : HasDerivWithinAt b b' S t := hasDerivWithinAt_pi.mpr hb
  exact HasFDerivAt.comp_hasDerivWithinAt (l := L) (l' := L) t hL hb'

end Carleman.PhysicalFiniteSpace
