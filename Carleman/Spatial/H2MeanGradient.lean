module

public import Carleman.Spatial.BoundedAffineSobolev
public import Carleman.Spatial.ConvexWeakPoincare

/-! Subtract the actual mean of each weak first derivative of an H² state.
Poincaré and genuine Hessian component contractions give the homogeneous
first-derivative error, without differentiability of any representative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def weakGradientMean (u : WeakSobolevJet d 2 (volume.restrict S) S) (i : Fin d) : ℝ :=
  (∫ x in S, derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)/volume.real S

theorem h2_gradient_mean_bound [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    (∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)-
      scalarConstantLp (volume.restrict S) (weakGradientMean u i)‖^2) ≤
      (2:ℝ)^d/2*D^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2 := by
  let H := WeakSobolevJet.field (2 : Fin 3) u
  let W := fun i j : Fin d => derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) H
  have hW (i j : Fin d) : ‖W i j‖ ≤ ‖H‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [derivativeComponent_ae (Sym.cons j (Sym.cons i Sym.nil)) H] with x hx
    rw [hx]
    exact PiLp.norm_apply_le _ _
  have hsum (i : Fin d) : (∑ j : Fin d, ‖W i j‖^2) ≤ (d:ℝ)*‖H‖^2 := by
    calc
      _ ≤ ∑ _j : Fin d, ‖H‖^2 := Finset.sum_le_sum fun j _ =>
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hW i j)
      _ = _ := by simp
  have he (i : Fin d) :
      ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)-
        scalarConstantLp (volume.restrict S) (weakGradientMean u i)‖^2 ≤
      (2:ℝ)^d/2*D^2*(∑ j : Fin d, ‖W i j‖^2) := by
    rw [norm_sub_scalarConstantLp_sq]
    exact convex_weak_mean_poincare hS hc hb hvol
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) (W i)
      (fun j => WeakSobolevJet.field_weak_derivative u (1 : Fin 2) (Sym.cons i Sym.nil) j) hD hdiam
  calc
    _ ≤ ∑ i : Fin d, (2:ℝ)^d/2*D^2*(∑ j : Fin d, ‖W i j‖^2) :=
      Finset.sum_le_sum fun i _ => he i
    _ ≤ ∑ _i : Fin d, (2:ℝ)^d/2*D^2*((d:ℝ)*‖H‖^2) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hsum i) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,H]; ring

end Carleman
