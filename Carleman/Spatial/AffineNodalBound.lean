module

public import Carleman.Spatial.SimplexMassIntegral
public import Carleman.Spatial.DerivativeFiberNorm
public import Carleman.Spatial.AffineWeakGradient

/-! A concrete nodal bound for affine states, with the cell volume cancelling
against the actual simplex L² mass. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

def affineNodalBound (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (∑ i, (p (T.points i))^2),Real.sqrt_nonneg _⟩

theorem affineNodalBound_abs (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell T.points) : |p x| ≤ affineNodalBound T p := by
  have hc (i : Fin (d+1)) : |p (T.points i)| ≤ (affineNodalBound T p : ℝ) := by
    have hi : (p (T.points i))^2 ≤ ∑ j, (p (T.points j))^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (p (T.points j))) (Finset.mem_univ i)
    change |p (T.points i)| ≤ Real.sqrt _
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (p (T.points j))))]
    exact hi
  have he := simplexNodalInterpolant_abs_le T (fun i => p (T.points i)) (affineNodalBound T p) hc hx
  rw [simplexNodalInterpolant_reproduces] at he
  exact he

theorem affineNodalBound_sq_mass (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    (affineNodalBound T p : ℝ)^2*volume.real (simplicialCell T.points) ≤
      ((d+1:ℝ)*(d+2))*(∫ x in simplicialCell T.points, (p x)^2) := by
  have hb := (integral_simplexNodalInterpolant_sq_bounds T (fun i => p (T.points i))).1
  rw [simplexNodalInterpolant_reproduces] at hb
  have hd : (0:ℝ) < (d+1:ℝ)*(d+2) := by positivity
  calc
    _ = ((d+1:ℝ)*(d+2))*(volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
        (∑ i, (p (T.points i))^2)) := by
      change (Real.sqrt _)^2*_ = _
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (p (T.points i))))]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hd.le

theorem affineNodalBound_energy : ∃ C > (0:ℝ),
    ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
      (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (q : ℝ),
      (q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖)^2*
        volume.real (simplicialCell T.points) ≤
      C*(q^4*(∫ x in simplicialCell T.points, (p x)^2)+
        q^2*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2)) := by
  obtain ⟨R,hR,hreverse⟩ := derivativeOneFiber_reverse_bound (d := d)
  let D : ℝ := (d+1:ℝ)*(d+2)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨2*D+8*R^2,by positivity,?_⟩
  intro T p q
  have hmass := affineNodalBound_sq_mass T p
  have hg : (∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2) =
      ‖derivativeOneFiber (affineScalarDerivative p)‖^2*volume.real (simplicialCell T.points) := by
    simp_rw [(affineScalar_hasFDerivAt p _).fderiv]
    simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm]
  have hsq : ‖affineScalarDerivative p‖^2 ≤ R^2*‖derivativeOneFiber (affineScalarDerivative p)‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hreverse (affineScalarDerivative p))
  have hgrad : ‖affineScalarDerivative p‖^2*volume.real (simplicialCell T.points) ≤
      R^2*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2) := by
    rw [hg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsq (measureReal_nonneg)
  have hsum : (q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖)^2 ≤
      2*q^4*(affineNodalBound T p : ℝ)^2+8*q^2*‖affineScalarDerivative p‖^2 := by
    nlinarith only [sq_nonneg (q^2*(affineNodalBound T p : ℝ)-2*q*‖affineScalarDerivative p‖)]
  have hi : 0 ≤ ∫ x in simplicialCell T.points, (p x)^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hj : 0 ≤ ∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ (2*q^4*(affineNodalBound T p : ℝ)^2+8*q^2*‖affineScalarDerivative p‖^2)*
        volume.real (simplicialCell T.points) := mul_le_mul_of_nonneg_right hsum measureReal_nonneg
    _ = 2*q^4*((affineNodalBound T p : ℝ)^2*volume.real (simplicialCell T.points))+
        8*q^2*(‖affineScalarDerivative p‖^2*volume.real (simplicialCell T.points)) := by ring
    _ ≤ 2*q^4*(D*(∫ x in simplicialCell T.points, (p x)^2))+
        8*q^2*(R^2*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity))
        (mul_le_mul_of_nonneg_left hgrad (by positivity))
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg R) (mul_nonneg (pow_nonneg (sq_nonneg q) 2) hi),
      mul_nonneg hD.le (mul_nonneg (sq_nonneg q) hj)]

end Carleman
