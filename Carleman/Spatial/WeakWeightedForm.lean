module

public import Carleman.Spatial.LaplacianCorrectionBounds
public import Carleman.Spatial.HeatNormSquare

/-! Exact weighted form identities on genuine first-order weak jets. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  [IsLocallyFiniteMeasure ν] {S : Set (SpatialCoordinates d)}

theorem weakFirstProduct_component_of_value (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u v : WeakSobolevJet d 1 ν S) (hv : WeakSobolevJet.value v=w.map (WeakSobolevJet.value u))
    (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v)=
      w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        (dw i).map (WeakSobolevJet.value u) := by
  have he : v=weakFirstProduct hS hν w dw hw hdw u :=
    WeakSobolevJet.value_injective hS hν (hv.trans (weakFirstProduct_value hS hν w dw hw hdw u).symm)
  rw [he,weakFirstProduct_component]

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem BoundedMultiplier.map_map_comm (w a : BoundedMultiplier ν) (u : Lp ℝ 2 ν) :
    a.map (w.map u)=w.map (a.map u) := by
  apply Lp.ext
  filter_upwards [a.map_ae (w.map u),w.map_ae (a.map u),w.map_ae u,a.map_ae u] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4,smul_comm]

set_option maxHeartbeats 800000 in
theorem weakGradientPairing_mul_twice (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u v z : WeakSobolevJet d 1 ν S)
    (hv : WeakSobolevJet.value v=w.map (WeakSobolevJet.value u))
    (hz : WeakSobolevJet.value z=w.map (WeakSobolevJet.value v)) :
    weakGradientPairing u z=(w.seminorm (WeakSobolevJet.field 1 u))^2+
      2*∑ i : Fin d, inner ℝ
        (w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)))
        ((dw i).map (WeakSobolevJet.value u)) := by
  have hG : (w.seminorm (WeakSobolevJet.field 1 u))^2=
      ∑ i : Fin d, ‖w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))‖^2 := by
    change ‖w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)‖^2= _
    rw [← real_inner_self_eq_norm_sq,firstDerivativeField_inner]
    simp only [derivativeComponent_multiplier,real_inner_self_eq_norm_sq]
  rw [hG,Finset.mul_sum,← Finset.sum_add_distrib,weakGradientPairing_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [weakFirstProduct_component_of_value hS hν w dw hw hdw v z hz i,
    weakFirstProduct_component_of_value hS hν w dw hw hdw u v hv i,hv,
    w.map_map_comm (dw i),BoundedMultiplier.map_add]
  simp only [inner_add_right]
  rw [w.inner_map_twice]
  simp only [← w.inner_map_left]
  ring

set_option maxHeartbeats 800000 in
theorem weakGradientPairing_weighted_lower (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u v z : WeakSobolevJet d 1 ν S)
    (hv : WeakSobolevJet.value v=w.map (WeakSobolevJet.value u))
    (hz : WeakSobolevJet.value z=w.map (WeakSobolevJet.value v))
    {q B : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hb : ∀ i, ∀ᵐ x ∂ν, |(dw i).value x| ≤ B*q*|w.value x|) :
    (1/2:ℝ)*(WeakSobolevJet.weightedNorm q w u)^2-
      ((1/2:ℝ)+2*(d:ℝ)*B^2)*(q*w.seminorm (WeakSobolevJet.value u))^2 ≤
        weakGradientPairing u z := by
  let U := w.seminorm (WeakSobolevJet.value u)
  let a := fun i : Fin d => w.map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
  let b := fun i : Fin d => (dw i).map (WeakSobolevJet.value u)
  have hbound (i : Fin d) : ‖b i‖ ≤ B*q*U :=
    (dw i).seminorm_le_of_weight_le w (B*q) (hb i) _
  have ht (i : Fin d) : (1/2:ℝ)*‖a i‖^2-2*(B*q*U)^2 ≤
      ‖a i‖^2+2*inner ℝ (a i) (b i) := by
    have hi := neg_le_of_abs_le (abs_real_inner_le_norm (a i) (b i))
    have hs : ‖b i‖^2 ≤ (B*q*U)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by dsimp [U]; positivity [apply_nonneg w.seminorm (WeakSobolevJet.value u)])).mpr (hbound i)
    nlinarith only [hi,hs,sq_nonneg (‖a i‖-2*‖b i‖)]
  have hG : (w.seminorm (WeakSobolevJet.field 1 u))^2=∑ i : Fin d, ‖a i‖^2 := by
    change ‖w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)‖^2= _
    rw [← real_inner_self_eq_norm_sq,firstDerivativeField_inner]
    simp only [derivativeComponent_multiplier,real_inner_self_eq_norm_sq,a]
  rw [WeakSobolevJet.heat_weightedNorm_sq,
    weakGradientPairing_mul_twice hS hν w dw hw hdw u v z hv hz,hG]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [← Finset.mul_sum,← Finset.mul_sum] at hs
  change (1/2:ℝ)*(q^2*U^2+∑ i : Fin d, ‖a i‖^2)-
      ((1/2:ℝ)+2*(d:ℝ)*B^2)*(q*U)^2 ≤
        (∑ i : Fin d, ‖a i‖^2)+2*∑ i : Fin d, inner ℝ (a i) (b i)
  convert hs using 1; ring

omit [IsLocallyFiniteMeasure ν] in
theorem weakGradientPairing_weighted_upper (w ξ : BoundedMultiplier ν)
    (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1) {q : ℝ} (hq : 0 ≤ q)
    (u v : WeakSobolevJet d 1 ν S) :
    |weakGradientPairing u v| ≤
      WeakSobolevJet.weightedNorm q w u*WeakSobolevJet.weightedNorm q ξ v := by
  have hu := WeakSobolevJet.weighted_component_le hq w u (1 : Fin 2)
  have hv := WeakSobolevJet.weighted_component_le hq ξ v (1 : Fin 2)
  norm_num only [Fin.val_one,Nat.sub_self,pow_zero,one_mul] at hu hv
  rw [weakGradientPairing_apply,← w.inner_inverse ξ hinv]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul hu hv (norm_nonneg _) (WeakSobolevJet.weightedNorm_nonneg _ _ _))

end Carleman
