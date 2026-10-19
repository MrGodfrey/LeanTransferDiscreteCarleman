module

public import Carleman.Spatial.BoxCompactSmoothDensity
public import Carleman.Weights.InteriorHeatGradientReturn

/-! A smooth representative of an original weak H1 value has exactly its classical spatial gradient. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.sobolevJet_component_ae (φ : SpatialTest S) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 φ.sobolevJet)
      =ᵐ[volume.restrict S] (fun x => fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  change derivativeComponent (Sym.cons i Sym.nil)
    ((OperatorMultiplier.const derivativeOneFiber).map φ.fderivLp) =ᵐ[volume.restrict S] _
  rw [derivativeOneFiber_component]
  filter_upwards [OperatorMultiplier.const_map_ae
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) φ.fderivLp,
    φ.fderivLp_ae] with x hx hf
  rw [hx,hf]
  rfl

theorem WeakSobolevJet.component_eq_smooth_derivative (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    {F : SpatialCoordinates d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hu : WeakSobolevJet.value u =ᵐ[volume.restrict S] F) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)
      =ᵐ[volume.restrict S] (fun x => fderiv ℝ F x (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  obtain ⟨η,hη⟩ := exists_spatialTest_eq_one_on_compact isOpen_univ hb.isCompact_closure (subset_univ _)
  let φ := η.mulSmooth hF
  have he : EqOn φ.value F S := by
    intro x hx
    change η.value x*F x=F x
    rw [hη x (subset_closure hx),one_mul]
  have hres : WeakSobolevJet.restrictSubdomain (subset_univ S) φ.sobolevJet=u := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    apply Lp.ext
    filter_upwards [WeakSobolevJet.restrictSubdomain_test_value_ae (subset_univ S) φ,hu,
      ae_restrict_mem hS.measurableSet] with x hr huv hx
    rw [hr,huv,he hx]
  have hc := WeakSobolevJet.restrictSubdomain_component_ae (subset_univ S) φ.sobolevJet u hres
    1 (Sym.cons i Sym.nil)
  have hd := (φ.sobolevJet_component_ae i).filter_mono
    (ae_mono (Measure.restrict_mono (subset_univ S) le_rfl))
  filter_upwards [hc,hd,ae_restrict_mem hS.measurableSet] with x hx hdx hmem
  rw [← hx,hdx]
  have heD := coordinateDerivative_eqOn_of_eqOn hS he (fun _ : Fin 1 => i) hmem
  simpa only [coordinateDerivative_one] using heD

theorem WeakSobolevJet.gradient_norm_sq_eq_smooth (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    {F : SpatialCoordinates d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hu : WeakSobolevJet.value u =ᵐ[volume.restrict S] F) :
    (fun x => ‖WeakSobolevJet.field 1 u x‖^2) =ᵐ[volume.restrict S] (fun x => ‖gradient F x‖^2) := by
  filter_upwards [ae_all_iff.mpr (fun i => WeakSobolevJet.component_eq_smooth_derivative hS hb u hF hu i),
    ae_all_iff.mpr (fun i => derivativeComponent_ae (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))]
    with x hcomp hfield
  rw [EuclideanSpace.real_norm_sq_eq,← spatial_directionalEnergy_gradient]
  trans ∑ i : Fin d, (WeakSobolevJet.field 1 u x (Sym.oneEquiv i))^2
  · exact (Equiv.sum_comp Sym.oneEquiv (fun α => (WeakSobolevJet.field 1 u x α)^2)).symm
  unfold directionalEnergy smoothD
  apply Finset.sum_congr rfl
  intro i _
  rw [show Sym.oneEquiv i=Sym.cons i Sym.nil from rfl,← hfield i,hcomp i]

end Carleman
