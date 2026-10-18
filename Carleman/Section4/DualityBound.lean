module

public import Carleman.Section4.ApproximationData
public import Carleman.Transfer.SpatialDuality

/-! The three terms of the complete spatial duality identity, estimated
in the actual positive/inverse Sobolev norms. No error rate is an input. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d (2*m) ν S) (hDV : D ≤ V)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction V X) (g : TimeGrid) (s : Orientation)
  (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
/-- Weighted Cauchy–Schwarz for the exact L² pairing and inverse weight. -/
theorem weighted_pairing_bound (v z : g.Sequence (Lp ℝ 2 ν)) :
    |g.pairing v z| ≤ g.l2Norm (ρ.nodeMap g w τ v)*g.l2Norm (ρ.neg.nodeMap g w (-τ) z) := by
  have hh := g.weighted_bilinear_sum_bound
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm)
    (fun i => (ρ.neg.multiplier w (-τ) (g.nodeTime i)).seminorm)
    (fun _ v z => inner ℝ v z) zero_le_one (fun i v z => ?_) v z
  · simpa only [one_mul,TimeGrid.pairing,TimeGrid.l2Norm,TimeGrid.weightedNorm,
      TimeGrid.weightedSq,BoundedMultiplier.seminorm_apply,SpatialProfile.nodeMap,
      LinearMap.coe_mk,AddHom.coe_mk,coe_normSeminorm] using hh
  · rw [← BoundedMultiplier.inner_inverse _ _
      (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ (g.nodeTime i))) v z]
    simpa only [one_mul,BoundedMultiplier.seminorm_apply] using abs_real_inner_le_norm
      ((ρ.multiplier w τ (g.nodeTime i)).map v)
      ((ρ.neg.multiplier w (-τ) (g.nodeTime i)).map z)

/-- The three exact terms give the a₀, a_E and stiffness-defect factors.
Y is an arbitrary actual domain sequence; its dual graph estimate is next. -/
theorem spatial_duality_bound
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ha : ∀ v z, a v z = a z v)
    (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v)+b z v)
    (μ : g.Sequence ℝ) {Cf aE a0 ηA : ℝ}
    (hCf : 0 ≤ Cf) (haE : 0 ≤ aE) (ha0 : 0 ≤ a0) (hη : 0 ≤ ηA)
    (happ : WeightedApproximation hS hν hV hD hDV r g ρ.neg w (-τ) aE a0)
    (hform : ∀ i v z, |Reconstruction.spatialForm a (μ i) v z| ≤
      Cf*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) v*
        conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) z)
    (hdef : ∀ i z v, |b z v| ≤
      ηA*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) (r.R z)*
        conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) (r.R v))
    (f : g.Sequence (Lp ℝ 2 ν)) (u Y : g.Sequence D) (z : g.Sequence X)
    (hu : ∀ (i : g.Index) (v : V), inner ℝ (s.difference g (fun j => (u j : Lp ℝ 2 ν)) i) (v : Lp ℝ 2 ν)+
      Reconstruction.spatialForm a (μ i) (Submodule.inclusion hDV (u i)) v = inner ℝ (f i) (v : Lp ℝ 2 ν))
    (hz : ∀ i, s.difference g z i+A (z i)+μ i • r.G (z i) = r.J (f i))
    (hY : ∀ (i : g.Index) (v : V), inner ℝ (s.opposite.difference g (fun j => (Y j : Lp ℝ 2 ν)) i) (v : Lp ℝ 2 ν)+
      Reconstruction.spatialForm a (μ i) (Submodule.inclusion hDV (Y i)) v =
        inner ℝ ((ρ.multiplier w τ (g.nodeTime i)).map
          ((ρ.multiplier w τ (g.nodeTime i)).map ((u i : Lp ℝ 2 ν)-r.RH (z i)))) (v : Lp ℝ 2 ν)) :
    (g.l2Norm (ρ.nodeMap g w τ (fun i => (u i : Lp ℝ 2 ν)-r.RH (z i))))^2 ≤
      (a0*g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+
        Cf*aE*energyNorm hS hν hV g ρ w τ (fun i => Submodule.inclusion hDV (u i)-r.R (z i))+
        ηA*(m+1+aE)*energyNorm hS hν hV g ρ w τ (fun i => r.R (z i)))*
        regularityNorm hS hν hD g ρ.neg w (-τ) Y := by
  let uV : g.Sequence V := fun i => Submodule.inclusion hDV (u i)
  let YV : g.Sequence V := fun i => Submodule.inclusion hDV (Y i)
  let e : g.Sequence V := fun i => uV i-r.R (z i)
  let η : g.Sequence V := fun i => YV i-r.Q (Y i : Lp ℝ 2 ν)
  let p := energySeminorm hS hν hV g ρ w τ
  let q := energySeminorm hS hν hV g ρ.neg w (-τ)
  have hp (i : g.Index) (v : V) : p i v = conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.multiplier w τ (g.nodeTime i)) v := conformingWeightedSeminorm_apply _ _ _ (w.nonneg _) _ _
  have hq (i : g.Index) (v : V) : q i v = conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.neg.multiplier w (-τ) (g.nodeTime i)) v := conformingWeightedSeminorm_apply _ _ _ (w.nonneg _) _ _
  have hid := r.spatial_weighted_duality g s a ha A b hA μ f uV YV z
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).linearMap)
    (fun i v z => ((ρ.multiplier w τ (g.nodeTime i)).inner_map_left v z).symm) hu hz hY
  have h₁ := weighted_pairing_bound g ρ w τ
    (s.difference g (fun i => (u i : Lp ℝ 2 ν))) (fun i => (η i : Lp ℝ 2 ν))
  have h₂ := g.weighted_bilinear_sum_bound p q
    (fun i v z => Reconstruction.spatialForm a (μ i) v z) hCf
    (fun i v z => by rw [hp,hq]; exact hform i v z) e η
  have h₃ := g.weighted_bilinear_sum_bound (fun i => (p i).comp r.R) (fun i => (q i).comp r.R)
    (fun _ z v => b z v) hη
    (fun i z v => by change |b z v| ≤ ηA*p i (r.R z)*q i (r.R v); rw [hp,hq]; exact hdef i z v)
    z (fun i => r.J (Y i : Lp ℝ 2 ν))
  have hη0 := happ.nodal_l2 hS hν hV hD hDV r g ρ.neg w (-τ) ha0 Y
  have hηE := happ.nodal_energy hS hν hV hD hDV r g ρ.neg w (-τ) haE Y
  have hQ := happ.nodal_Q hS hν hV hD hDV r g ρ.neg w (-τ) haE Y
  have h₁' := h₁.trans (mul_le_mul_of_nonneg_left hη0 (g.l2Norm_nonneg _))
  have h₂' := h₂.trans (mul_le_mul_of_nonneg_left hηE
    (mul_nonneg hCf (g.weightedNorm_nonneg p e)))
  have h₃' := h₃.trans (mul_le_mul_of_nonneg_left hQ
    (mul_nonneg hη (g.weightedNorm_nonneg (fun i => (p i).comp r.R) z)))
  have hsum := add_le_add (add_le_add (le_abs_self _ |>.trans h₁')
    (le_abs_self _ |>.trans h₂')) (le_abs_self _ |>.trans h₃')
  have heq : g.weightedNorm p e = energyNorm hS hν hV g ρ w τ
      (fun i => Submodule.inclusion hDV (u i)-r.R (z i)) := rfl
  have hzq : g.weightedNorm (fun i => (p i).comp r.R) z =
      energyNorm hS hν hV g ρ w τ (fun i => r.R (z i)) := rfl
  rw [heq,hzq] at hsum
  rw [g.l2Norm_sq]
  change g.dt*(∑ i, ‖(ρ.multiplier w τ (g.nodeTime i)).linearMap ((uV i : Lp ℝ 2 ν)-r.RH (z i))‖^2) ≤ _
  rw [hid]
  simp only [Finset.sum_add_distrib,mul_add] at ⊢
  exact hsum.trans_eq (by ring)

end Carleman.Section4
