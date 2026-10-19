module

public import Carleman.Spatial.InwardMollification

/-! Every original weak H² jet on a bounded open convex domain has one
actual globally smooth sequence converging in all components on the entire
closure. L² zero extension is never asserted to be an H² extension. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.inward_mollification_strong_h2
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S)
    {a : SpatialCoordinates d} (ha : a ∈ S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      let U := inwardMollification a φ (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))
      (∀ n, ContDiff ℝ ∞ (U n)) ∧
      Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => U n x-zeroExtendLp hS.measurableSet (WeakSobolevJet.value u) x)) atTop (𝓝 0) ∧
      (∀ v : Fin 1 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => coordinateDerivative v (U n) x-
          zeroExtendLp hS.measurableSet (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u)) x)) atTop (𝓝 0)) ∧
      (∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => coordinateDerivative v (U n) x-
          zeroExtendLp hS.measurableSet (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u)) x)) atTop (𝓝 0)) := by
  obtain ⟨φ,_,hφ,hinside⟩ := exists_inward_mollifier_sequence hS hc hb ha
  refine ⟨φ,hφ,fun n => inwardMollification_smooth _ _ _ n,?_,?_,?_⟩
  · simpa only [pow_zero,one_mul] using inwardMollification_scaled_L2_error_tendsto a hφ
      (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) 0 (closure S)
  · intro v
    let w := zeroExtendLp hS.measurableSet
      (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u))
    apply (inwardMollification_scaled_L2_error_tendsto a hφ w 1 (closure S)).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply bochnerL2Norm_congr_ae
    filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with x hx
    have hv : (fun _ : Fin 1 => v 0)=v := by funext i; fin_cases i; rfl
    have he := ((WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil (v 0)).zeroExtend
      hS.measurableSet).coordinate_one_inwardMollification a φ n x (hinside n x hx)
    simp only [hv] at he
    change coordinateDerivative v (inwardMollification a φ (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) n) x=
      inwardRatio n*inwardMollification a φ w n x at he
    rw [he,pow_one]
  · intro v
    let w := zeroExtendLp hS.measurableSet
      (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u))
    apply (inwardMollification_scaled_L2_error_tendsto a hφ w 2 (closure S)).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply bochnerL2Norm_congr_ae
    filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with x hx
    have hv : ![v 0,v 1]=v := by funext i; fin_cases i <;> rfl
    have he := ((WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil (v 0)).zeroExtend
      hS.measurableSet).coordinate_two_inwardMollification
        ((WeakSobolevJet.field_weak_derivative u (1 : Fin 2) (Sym.cons (v 0) Sym.nil) (v 1)).zeroExtend hS.measurableSet)
        a φ n x (hinside n x hx)
    rw [hv] at he
    change coordinateDerivative v (inwardMollification a φ (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) n) x=
      (inwardRatio n)^2*inwardMollification a φ w n x at he
    rw [he]

end Carleman
