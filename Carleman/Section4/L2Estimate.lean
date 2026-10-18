module

public import Carleman.Section4.DualityBound
public import Carleman.Section4.EnergyEstimate

/-! Aubin–Nitsche on the actual periodic Euler equations. The opposite
Euler solution is constructed using Section 3, with the inverse weight. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X)
  (g : TimeGrid) (s : Orientation) (ρ : SpatialProfile ν) (w : TimeWeight)
  (L τ aE a0 ηA K : ℝ)

/-- The L² half of original Lemma 4.1 for every actual pair of solutions. -/
def L2Estimate : Prop :=
  ∀ (f : g.Sequence (Lp ℝ 2 ν)) (u : g.Sequence a.model.domain) (z : g.Sequence X),
    a.model.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f →
    (∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*m) • r.G (z i) = r.J (f i)) →
    g.l2Norm (ρ.nodeMap g w τ (fun i => (u i : Lp ℝ 2 ν)-r.RH (z i))) ≤
      K*(a0+aE^2+ηA)*g.l2Norm (ρ.nodeMap g w τ f)

/-- Scalar rate comparison used only after the three genuine duality terms
have been bounded. The mixed defect term costs no extra rate. -/
theorem duality_rate_coefficient {aE a0 ηA Cf Ke Kg : ℝ} (m : ℕ)
    (haE1 : aE ≤ 1) (ha0 : 0 ≤ a0) (hη : 0 ≤ ηA)
    (hCf : 0 ≤ Cf) (hKe : 0 ≤ Ke) (hKg : 0 ≤ Kg) :
    a0*Kg+Cf*aE*Ke*(aE+ηA)+ηA*(m+1+aE)*Ke ≤
      (Kg+Cf*Ke+Ke*(m+2))*(a0+aE^2+ηA) := by
  have he : aE*(aE+ηA) ≤ aE^2+ηA := by
    nlinarith only [mul_le_mul_of_nonneg_right haE1 hη]
  have hm : (m+1+aE:ℝ) ≤ m+2 := by linarith only [haE1]
  have h₁ : a0*Kg ≤ Kg*(a0+aE^2+ηA) := by
    nlinarith only [mul_nonneg hKg (add_nonneg (sq_nonneg aE) hη)]
  have h₂ : Cf*aE*Ke*(aE+ηA) ≤ Cf*Ke*(a0+aE^2+ηA) := by
    have hrate : aE^2+ηA ≤ a0+aE^2+ηA := by linarith only [ha0]
    have hh := mul_le_mul_of_nonneg_left (he.trans hrate) (mul_nonneg hCf hKe)
    nlinarith only [hh]
  have h₃ : ηA*(m+1+aE)*Ke ≤ Ke*(m+2)*(a0+aE^2+ηA) := by
    have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hη hKe)
    have hh' := mul_nonneg (mul_nonneg hKe (show (0:ℝ) ≤ m+2 by positivity))
      (add_nonneg ha0 (sq_nonneg aE))
    nlinarith only [hh,hh']
  nlinarith only [h₁,h₂,h₃]

/-- Complete L² rate from the proved energy estimate, original N3 for the
inverse weight, A3 and N1, and the two proved Euler graph estimates. -/
theorem l2_estimate_of_energy {aE a0 ηA Cf Ke Kg : ℝ}
    (haE : 0 ≤ aE) (haE1 : aE ≤ 1) (ha0 : 0 ≤ a0) (hη : 0 ≤ ηA)
    (hCf : 0 ≤ Cf) (hKe : 0 ≤ Ke) (hKg : 0 ≤ Kg)
    (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a.scalarForm (r.R z) (r.R v)+b z v)
    (happ : WeightedApproximation hS hν a.sobolev hD a.domain_le r g ρ.neg w (-τ) aE a0)
    (hform : ∀ i v z, |Reconstruction.spatialForm a.bilinearForm ((L*w.nodes g i)^(2*m)) v z| ≤
      Cf*conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) v*
        conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) z)
    (hdef : ∀ i z v, |b z v| ≤
      ηA*conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) (r.R z)*
        conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) (r.R v))
    (he : EnergyEstimate a r A g s ρ w L τ aE ηA Ke)
    (hg : Section3.EulerEstimate hS hν a.model hD g s w ρ L τ Kg)
    (hd : Section3.EulerEstimate hS hν a.model hD g s.opposite w ρ.neg L (-τ) Kg) :
    L2Estimate a r A g s ρ w L τ aE a0 ηA ((Kg+Cf*Ke+Ke*(m+2))*Kg) := by
  intro f u z hu hz
  let err : g.Sequence (Lp ℝ 2 ν) := fun i => (u i : Lp ℝ 2 ν)-r.RH (z i)
  let k := ρ.nodeMap g w τ (ρ.nodeMap g w τ err)
  obtain ⟨Y,hY,_⟩ := (hd k).1
  have hk : ρ.neg.nodeMap g w (-τ) k = ρ.nodeMap g w τ err := by
    funext i
    apply BoundedMultiplier.map_inverse _ _
    filter_upwards [] with x
    rw [mul_comm]
    exact ρ.multiplier_inverse w τ (g.nodeTime i) x
  have hreg : regularityNorm hS hν hD g ρ.neg w (-τ) Y ≤ Kg*g.l2Norm (ρ.nodeMap g w τ err) := by
    have hh := (hd k).2 Y hY
    rw [hk] at hh
    have hn := g.l2Norm_nonneg (ρ.neg.nodeMap g w (-τ) (s.opposite.difference g (fun i => (Y i : Lp ℝ 2 ν))))
    linarith only [hh,hn]
  have htime : g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) ≤
      Kg*g.l2Norm (ρ.nodeMap g w τ f) := by
    have hh := (hg f).2 u hu
    have hn := regularityNorm_nonneg hS hν hD g ρ w τ u
    linarith only [hh,hn]
  obtain ⟨herr,hstate⟩ := he f u z hu hz
  have hb := spatial_duality_bound hS hν a.sobolev hD a.domain_le r g s ρ w τ
    a.bilinearForm (fun v z => a.symmetric _ _) A b hA
    (fun i => (L*w.nodes g i)^(2*m)) hCf haE ha0 hη happ hform hdef f u Y z
    (fun i v => Reconstruction.spatial_continuous_test g s a.domain_le a.model.operator a.bilinearForm
      (fun u v => (a.operator_test u v).symm) _ f u (fun i => congrFun hu i) i v)
    hz
    (fun i v => Reconstruction.spatial_continuous_test g s.opposite a.domain_le a.model.operator a.bilinearForm
      (fun u v => (a.operator_test u v).symm) _ k Y (fun i => congrFun hY i) i v)
  let F := g.l2Norm (ρ.nodeMap g w τ f)
  let E := g.l2Norm (ρ.nodeMap g w τ err)
  let R := regularityNorm hS hν hD g ρ.neg w (-τ) Y
  have hF : 0 ≤ F := g.l2Norm_nonneg _
  have hE : 0 ≤ E := g.l2Norm_nonneg _
  have hR : 0 ≤ R := regularityNorm_nonneg hS hν hD g ρ.neg w (-τ) Y
  have hcoeff := duality_rate_coefficient m haE1 ha0 hη hCf hKe hKg
  have hbound := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left htime ha0)
    (mul_le_mul_of_nonneg_left herr (mul_nonneg hCf haE)))
    (mul_le_mul_of_nonneg_left hstate (mul_nonneg hη (show (0:ℝ) ≤ m+1+aE by positivity)))
  have hbound' : a0*g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+
      Cf*aE*energyNorm hS hν a.sobolev g ρ w τ (fun i => Submodule.inclusion a.domain_le (u i)-r.R (z i))+
      ηA*(m+1+aE)*energyNorm hS hν a.sobolev g ρ w τ (fun i => r.R (z i)) ≤
      (Kg+Cf*Ke+Ke*(m+2))*(a0+aE^2+ηA)*F :=
    hbound.trans (by
      convert mul_le_mul_of_nonneg_right hcoeff hF using 1
      dsimp only [F]
      ring)
  have hfinal : E^2 ≤ ((Kg+Cf*Ke+Ke*(m+2))*Kg)*(a0+aE^2+ηA)*F*E := by
    have hc : 0 ≤ (Kg+Cf*Ke+Ke*(m+2))*(a0+aE^2+ηA)*F := by positivity
    exact hb.trans ((mul_le_mul_of_nonneg_right hbound' hR).trans
      ((mul_le_mul_of_nonneg_left hreg hc).trans_eq (by ring)))
  change E ≤ ((Kg+Cf*Ke+Ke*(m+2))*Kg)*(a0+aE^2+ηA)*F
  by_cases hzero : E = 0
  · rw [hzero]
    positivity
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith only [hfinal,hp]

end Carleman.Section4
