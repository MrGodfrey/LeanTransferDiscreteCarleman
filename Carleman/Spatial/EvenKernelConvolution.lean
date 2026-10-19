module

public import Carleman.Spatial.EvenSpatialMollifier
public import Carleman.Spatial.StrongMollifierLimit

/-! Actual convolution identities for coordinate symmetrization. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution Topology
namespace Carleman
variable {d : ℕ}
namespace SpatialTest

theorem reflected_kernel_convolution (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (x : SpatialCoordinates d) :
    ((κ.reflectCoordinate r 0).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x=
      (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (coordinateReflectionLp r 0 u))
        (coordinateSignFlip r x) := by
  change (∫ s, κ.value (coordinateReflection r 0 s)*u (x-s))=
    ∫ s, κ.value s*coordinateReflectionLp r 0 u (coordinateSignFlip r x-s)
  have hchange := (coordinateReflection_measurePreserving r 0).integral_comp
    (coordinateReflection r 0).toMeasurableEquiv.measurableEmbedding
    (fun s => κ.value (coordinateReflection r 0 s)*u (x-s))
  rw [← hchange]
  apply integral_congr_ae
  have hcoe := (Measure.measurePreserving_sub_left volume (coordinateSignFlip r x)).quasiMeasurePreserving.ae
    (coordinateReflectionLp_ae r 0 u)
  filter_upwards [hcoe] with s hs
  change coordinateReflectionLp r 0 u (coordinateSignFlip r x-s)=
    u (coordinateReflection r 0 (coordinateSignFlip r x-s)) at hs
  rw [coordinateReflection_involutive,hs,coordinateReflection_zero,coordinateReflection_zero,
    map_sub,coordinateSignFlip_involutive]

theorem evenCoordinate_convolution (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (x : SpatialCoordinates d) :
    ((κ.evenCoordinate r).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x=
      ((κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] u) x+
        (κ.value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (coordinateReflectionLp r 0 u))
          (coordinateSignFlip r x))/2 := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hi : Integrable (fun s => κ.value s*u (x-s)) volume :=
    κ.compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) κ.smooth.continuous hu x
  have hir : Integrable (fun s => (κ.reflectCoordinate r 0).value s*u (x-s)) volume :=
    (κ.reflectCoordinate r 0).compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (κ.reflectCoordinate r 0).smooth.continuous hu x
  rw [← reflected_kernel_convolution κ r u x]
  change (∫ s, ((1/2)*(κ.value s+(κ.reflectCoordinate r 0).value s))*u (x-s))=
    ((∫ s, κ.value s*u (x-s))+(∫ s, (κ.reflectCoordinate r 0).value s*u (x-s)))/2
  simp_rw [show ∀ s, ((1/2)*(κ.value s+(κ.reflectCoordinate r 0).value s))*u (x-s)=
    (1/2)*(κ.value s*u (x-s)+(κ.reflectCoordinate r 0).value s*u (x-s)) from fun s => by ring]
  rw [integral_const_mul,integral_add hi hir]
  ring

end SpatialTest
end Carleman
