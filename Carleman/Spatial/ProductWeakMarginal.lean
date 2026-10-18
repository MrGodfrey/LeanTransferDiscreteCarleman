module

public import Carleman.Spatial.TensorSpatialTest
public import Carleman.Spatial.CountableWeakTests
public import Carleman.Spatial.RealL2Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-! Test the genuine product-domain weak derivative with tensor tests and
apply the fundamental lemma in the transverse variables. Every Fubini
exchange uses actual integrable products of L² functions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem product_weak_marginal [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (g : TimeGrid)
    (f v : Lp ℝ 2 ((volume.restrict S).prod g.timeMeasure))
    (hw : IsWeakSpatialDerivative ((volume.restrict S).prod g.timeMeasure)
      (S ×ˢ Ioo 0 g.period) (0,1) f v)
    (ψ : SpatialTest (Ioo 0 g.period)) :
    ∀ᵐ x ∂volume.restrict S,
      (∫ t, deriv ψ.value t*f (x,t) ∂g.timeMeasure)=
        -(∫ t, ψ.value t*v (x,t) ∂g.timeMeasure) := by
  let μ := volume.restrict S
  have hA : Integrable (fun p : SpatialCoordinates d × ℝ => deriv ψ.value p.2*f p)
      (μ.prod g.timeMeasure) :=
    memLp_one_iff_integrable.mp (((ψ.memLp_derivative g.timeMeasure 1).comp_snd μ).mul (Lp.memLp f))
  have hB : Integrable (fun p : SpatialCoordinates d × ℝ => ψ.value p.2*v p)
      (μ.prod g.timeMeasure) :=
    memLp_one_iff_integrable.mp (((ψ.memLp g.timeMeasure).comp_snd μ).mul (Lp.memLp v))
  let M : SpatialCoordinates d → ℝ := fun x =>
    ∫ t, (deriv ψ.value t*f (x,t)+ψ.value t*v (x,t)) ∂g.timeMeasure
  have hM : Integrable M μ := (hA.add hB).integral_prod_left
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hM.locallyIntegrable.locallyIntegrableOn S) (fun φ hs hc hsup => by
      let Φ : SpatialTest S := ⟨φ,hs,hc,hsup⟩
      have hi1 : Integrable (fun p : SpatialCoordinates d × ℝ => φ p.1*deriv ψ.value p.2*f p)
          (μ.prod g.timeMeasure) := by
        have he := memLp_one_iff_integrable.mp
          (((Φ.tensor ψ).memLp_derivative (μ.prod g.timeMeasure) (0,1)).mul (Lp.memLp f))
        change Integrable (fun p => fderiv ℝ (Φ.tensor ψ).value p (0,1)*f p) (μ.prod g.timeMeasure) at he
        simp_rw [SpatialTest.tensor_interval_derivative] at he
        exact he
      have hi2 : Integrable (fun p : SpatialCoordinates d × ℝ => φ p.1*ψ.value p.2*v p)
          (μ.prod g.timeMeasure) :=
        memLp_one_iff_integrable.mp (((Φ.tensor ψ).memLp (μ.prod g.timeMeasure)).mul (Lp.memLp v))
      have hmul : Integrable (fun p : SpatialCoordinates d × ℝ =>
          φ p.1*(deriv ψ.value p.2*f p+ψ.value p.2*v p)) (μ.prod g.timeMeasure) := by
        convert hi1.add hi2 using 1
        funext p
        dsimp
        ring
      have hid := (IsWeakSpatialDerivative.iff_integral.mp hw) (Φ.tensor ψ)
      simp_rw [SpatialTest.tensor_interval_derivative] at hid
      change (∫ x, φ x*M x ∂μ)=0
      calc
        _ = ∫ x, ∫ t, φ x*(deriv ψ.value t*f (x,t)+ψ.value t*v (x,t)) ∂g.timeMeasure ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => (integral_const_mul (φ x) _).symm
        _ = ∫ p, φ p.1*(deriv ψ.value p.2*f p+ψ.value p.2*v p) ∂μ.prod g.timeMeasure :=
          (integral_prod _ hmul).symm
        _ = 0 := by
          simp_rw [mul_add]
          rw [integral_add]
          · change (∫ p, φ p.1*(deriv ψ.value p.2*f p) ∂μ.prod g.timeMeasure)+
              (∫ p, φ p.1*(ψ.value p.2*v p) ∂μ.prod g.timeMeasure)=0
            have he : (∫ p, φ p.1*(deriv ψ.value p.2*f p) ∂μ.prod g.timeMeasure)=
                -(∫ p, φ p.1*(ψ.value p.2*v p) ∂μ.prod g.timeMeasure) := by
              simpa only [SpatialTest.tensor,Φ,mul_assoc] using hid
            rw [he,neg_add_cancel]
          · simpa only [mul_assoc] using hi1
          · simpa only [mul_assoc] using hi2)
  filter_upwards [hz,ae_restrict_mem hS.measurableSet,hA.prod_right_ae,hB.prod_right_ae]
    with x hx hmem ha hb
  have he := hx hmem
  change (∫ t, deriv ψ.value t*f (x,t)+ψ.value t*v (x,t) ∂g.timeMeasure)=0 at he
  rw [integral_add ha hb] at he
  exact eq_neg_of_add_eq_zero_left he

end Carleman
