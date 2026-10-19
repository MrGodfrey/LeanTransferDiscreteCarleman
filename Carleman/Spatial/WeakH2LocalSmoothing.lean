module

public import Carleman.Spatial.LocalStrongMollification
public import Carleman.Spatial.MollifiedHessianEnergy

/-! Actual smooth approximations to every original weak H² jet on compact
interior subsets, simultaneously in value and every first/second derivative
component. No smooth representative of the input is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.local_mollification_strong_h2
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    let U := fun n => zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
    (∀ n, ContDiff ℝ ∞ (U n)) ∧
    Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x => U n x-WeakSobolevJet.value u x))
      atTop (𝓝 0) ∧
    (∀ i : Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      fderiv ℝ (U n) x (EuclideanSpace.basisFun (Fin d) ℝ i)-
        derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)) atTop (𝓝 0)) ∧
    (∀ i j : Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x =>
      iteratedFDeriv ℝ 2 (U n) x ![EuclideanSpace.basisFun (Fin d) ℝ i,EuclideanSpace.basisFun (Fin d) ℝ j]-
        derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 u) x)) atTop (𝓝 0)) := by
  intro U
  have hreplace (w : Lp ℝ 2 (volume.restrict S)) (F : ℕ → SpatialCoordinates d → ℝ)
      (ht : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
        (fun x => F n x-zeroExtendLp hS.measurableSet w x)) atTop (𝓝 0)) :
      Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x => F n x-w x)) atTop (𝓝 0) := by
    apply ht.congr'
    apply Filter.Eventually.of_forall
    intro n
    apply bochnerL2Norm_congr_ae
    filter_upwards [(zeroExtendLp_ae_restrict hS.measurableSet w).filter_mono
      (ae_mono (Measure.restrict_mono hKS le_rfl))] with x hx
    rw [hx]
  refine ⟨fun n => (spatialMollifier d n).smooth_convolution _,?_,?_,?_⟩
  · exact hreplace (WeakSobolevJet.value u) U
      (spatialMollifier_L2_error_restrict_tendsto (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) K)
  · intro i
    exact hreplace (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) _
      (((WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil i).zeroExtend hS.measurableSet).local_mollification_strong_first hS hK hKS)
  · intro i j
    exact hreplace (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 u)) _
      (((WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil i).zeroExtend hS.measurableSet).local_mollification_strong_second hS hK hKS
          ((WeakSobolevJet.field_weak_derivative u (1 : Fin 2) (Sym.cons i Sym.nil) j).zeroExtend hS.measurableSet))

end Carleman
