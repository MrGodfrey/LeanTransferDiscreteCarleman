module

public import Carleman.Transfer.SpatialConsistency
public import Carleman.Periodic.SeminormAlgebra

/-! Weighted Cea argument on the conforming reconstruction. The inputs are
nodewise form/coercivity, N1 stiffness defect and N4 superapproximation, plus
the proved time-pairing lower bound. No spatial error estimate is an input.
All norms below are the actual dt sums of the supplied spatial seminorms. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Reconstruction
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Reconstruction V X)

/-- N4 superapproximation and the genuine σ² multiplication estimate give
the inverse-weight stability of the reconstructed test. -/
theorem spatial_test_stability (p q : Seminorm ℝ V) (T : X →ₗ[ℝ] X)
    (M : V →ₗ[ℝ] V) {ε CM : ℝ}
    (hsuper : ∀ z, q (r.R (T z)-M (r.R z)) ≤ ε*p (r.R z))
    (hmul : ∀ v, q (M v) ≤ CM*p v) (z : X) :
    q (r.R (T z)) ≤ (ε+CM)*p (r.R z) := by
  calc
    _ = q ((r.R (T z)-M (r.R z))+M (r.R z)) := by rw [sub_add_cancel]
    _ ≤ q (r.R (T z)-M (r.R z))+q (M (r.R z)) := map_add_le_add _ _ _
    _ ≤ ε*p (r.R z)+CM*p (r.R z) := add_le_add (hsuper z) (hmul _)
    _ = _ := by ring

/-- Testing the exact error equation retains the mass margin, test defect,
and stiffness defect before summation or absorption. -/
theorem spatial_test_node (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : ℝ)
    (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (p q : Seminorm ℝ V)
    (T : X →ₗ[ℝ] X) (M : V →ₗ[ℝ] V)
    {c B Cf Ct ε ηA : ℝ} (hCf : 0 ≤ Cf) (hηA : 0 ≤ ηA)
    (hform : ∀ v z, |spatialForm a μ v z| ≤ Cf*p v*q z)
    (hdefect : ∀ v z, |b v z| ≤ ηA*p (r.R v)*q (r.R z))
    (htest : ∀ z, q (r.R (T z)) ≤ Ct*p (r.R z))
    (hsuper : ∀ z, q (r.R (T z)-M (r.R z)) ≤ ε*p (r.R z))
    (e j : X) (v : V) (d : X) (mass : ℝ)
    (hcoer : c*(p (r.R e))^2+B*mass^2 ≤ spatialForm a μ (r.R e) (M (r.R e)))
    (heq : inner ℝ d (T e)+spatialForm a μ (r.R e) (r.R (T e))+b e (T e) =
      spatialForm a μ v (r.R (T e))-b j (T e)) :
    c*(p (r.R e))^2+B*mass^2 ≤ -inner ℝ d (T e)+
      (Cf*Ct)*(p v*p (r.R e))+(ηA*Ct)*(p (r.R j)*p (r.R e))+
      (Cf*ε+ηA*Ct)*(p (r.R e))^2 := by
  have hv : |spatialForm a μ v (r.R (T e))| ≤ Cf*Ct*(p v*p (r.R e)) := by
    exact (hform _ _).trans ((mul_le_mul_of_nonneg_left (htest e)
      (mul_nonneg hCf (apply_nonneg _ _))).trans_eq (by ring))
  have hj : |b j (T e)| ≤ ηA*Ct*(p (r.R j)*p (r.R e)) := by
    exact (hdefect _ _).trans ((mul_le_mul_of_nonneg_left (htest e)
      (mul_nonneg hηA (apply_nonneg _ _))).trans_eq (by ring))
  have hb : |b e (T e)| ≤ ηA*Ct*(p (r.R e))^2 := by
    exact (hdefect _ _).trans ((mul_le_mul_of_nonneg_left (htest e)
      (mul_nonneg hηA (apply_nonneg _ _))).trans_eq (by ring))
  have hs : |spatialForm a μ (r.R e) (r.R (T e)-M (r.R e))| ≤ Cf*ε*(p (r.R e))^2 := by
    exact (hform _ _).trans ((mul_le_mul_of_nonneg_left (hsuper e)
      (mul_nonneg hCf (apply_nonneg _ _))).trans_eq (by ring))
  rw [spatialForm_sub_right] at hs
  linarith [le_abs_self (spatialForm a μ v (r.R (T e))), neg_le_abs (b j (T e)),
    neg_le_abs (b e (T e)), neg_le_abs (spatialForm a μ (r.R e) (r.R (T e))-
      spatialForm a μ (r.R e) (M (r.R e)))]

/-- The actual periodic weighted Cea estimate. A3's mass margin cancels the
N4 time variation; small test and stiffness defects consume at most c/2. -/
theorem spatial_test_energy_bound (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : g.Sequence ℝ)
    (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (p q : g.Index → Seminorm ℝ V)
    (T : g.Index → X →ₗ[ℝ] X) (M : g.Index → V →ₗ[ℝ] V)
    {c B Cf Ct ε ηA : ℝ} (hc : 0 < c) (hCf : 0 ≤ Cf) (hCt : 0 ≤ Ct) (hηA : 0 ≤ ηA)
    (hsmall : Cf*ε+ηA*Ct ≤ c/2)
    (hform : ∀ i v z, |spatialForm a (μ i) v z| ≤ Cf*p i v*q i z)
    (hdefect : ∀ i v z, |b v z| ≤ ηA*p i (r.R v)*q i (r.R z))
    (htest : ∀ i z, q i (r.R (T i z)) ≤ Ct*p i (r.R z))
    (hsuper : ∀ i z, q i (r.R (T i z)-M i (r.R z)) ≤ ε*p i (r.R z))
    (e j : g.Sequence X) (v : g.Sequence V) (mass : g.Index → ℝ)
    (hcoer : ∀ i, c*(p i (r.R (e i)))^2+B*(mass i)^2 ≤
      spatialForm a (μ i) (r.R (e i)) (M i (r.R (e i))))
    (htime : -B*(g.dt*∑ i, (mass i)^2) ≤
      g.pairing (s.difference g e) (fun i => T i (e i)))
    (heq : ∀ i, inner ℝ (s.difference g e i) (T i (e i))+
      spatialForm a (μ i) (r.R (e i)) (r.R (T i (e i)))+b (e i) (T i (e i)) =
      spatialForm a (μ i) (v i) (r.R (T i (e i)))-b (j i) (T i (e i))) :
    g.weightedNorm p (g.map r.R e) ≤
      (2/c)*Ct*(Cf*g.weightedNorm p v+ηA*g.weightedNorm p (g.map r.R j)) := by
  have hn := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    r.spatial_test_node a (μ i) b (p i) (q i) (T i) (M i) hCf hηA
      (hform i) (hdefect i) (htest i) (hsuper i) (e i) (j i) (v i)
      (s.difference g e i) (mass i) (hcoer i) (heq i)) g.dt_pos.le
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hn
  have hcs₁ := mul_le_mul_of_nonneg_left (g.weightedNorm_product_sum p p v (g.map r.R e))
    (mul_nonneg hCf hCt)
  have hcs₂ := mul_le_mul_of_nonneg_left
    (g.weightedNorm_product_sum p p (g.map r.R j) (g.map r.R e)) (mul_nonneg hηA hCt)
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (g.weightedNorm p (g.map r.R e)))
  have hsq := g.weightedNorm_sq p (g.map r.R e)
  change _ = g.dt*∑ i, (p i (r.R (e i)))^2 at hsq
  change -B*(g.dt*∑ i, (mass i)^2) ≤
    g.dt*∑ i, inner ℝ (s.difference g e i) (T i (e i)) at htime
  change Cf*Ct*(g.dt*∑ i, p i (v i)*p i (r.R (e i))) ≤ _ at hcs₁
  change ηA*Ct*(g.dt*∑ i, p i (r.R (j i))*p i (r.R (e i))) ≤ _ at hcs₂
  have hn' : c*(g.weightedNorm p (g.map r.R e))^2+B*(g.dt*∑ i, (mass i)^2) ≤
      -(g.dt*∑ i, inner ℝ (s.difference g e i) (T i (e i)))+
      Cf*Ct*(g.dt*∑ i, p i (v i)*p i (r.R (e i)))+
      ηA*Ct*(g.dt*∑ i, p i (r.R (j i))*p i (r.R (e i)))+
      (Cf*ε+ηA*Ct)*(g.weightedNorm p (g.map r.R e))^2 := by
    rw [hsq]
    nlinarith only [hn]
  have henergy : (c/2)*(g.weightedNorm p (g.map r.R e))^2 ≤
      Ct*(Cf*g.weightedNorm p v+ηA*g.weightedNorm p (g.map r.R j))*
        g.weightedNorm p (g.map r.R e) := by nlinarith only [hn',htime,hcs₁,hcs₂,hs]
  have hN := g.weightedNorm_nonneg p (g.map r.R e)
  have hR : 0 ≤ Ct*(Cf*g.weightedNorm p v+ηA*g.weightedNorm p (g.map r.R j)) :=
    mul_nonneg hCt (add_nonneg (mul_nonneg hCf (g.weightedNorm_nonneg p v))
      (mul_nonneg hηA (g.weightedNorm_nonneg p (g.map r.R j))))
  have hlin : (c/2)*g.weightedNorm p (g.map r.R e) ≤
      Ct*(Cf*g.weightedNorm p v+ηA*g.weightedNorm p (g.map r.R j)) := by
    by_cases hz : g.weightedNorm p (g.map r.R e) = 0
    · simpa only [hz,mul_zero] using hR
    · have hp := lt_of_le_of_ne hN (Ne.symm hz)
      nlinarith only [henergy,hp]
  calc
    _ ≤ (Ct*(Cf*g.weightedNorm p v+ηA*g.weightedNorm p (g.map r.R j)))/(c/2) :=
      (le_div_iff₀ (show 0 < c/2 by positivity)).mpr (by nlinarith only [hlin])
    _ = _ := by ring

end Carleman.Reconstruction
