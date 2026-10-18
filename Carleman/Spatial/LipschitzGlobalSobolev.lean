module

public import Carleman.Spatial.LipschitzWeakDerivative
public import Carleman.Spatial.FirstOrderSobolevJet

/-! Global weak H¹ membership from actual Lipschitz and a.e. derivative data. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem weakSpatialDerivative_of_lipschitz_full {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (e : SpatialCoordinates d)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hu : u =ᵐ[volume] f) (hv : v =ᵐ[volume] (fun x => lineDeriv ℝ f x e)) :
    IsWeakSpatialDerivative volume Set.univ e u v := by
  rw [IsWeakSpatialDerivative.iff_integral]
  intro φ
  obtain ⟨D,hφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  have hi := hf.integral_lineDeriv_mul_eq (μ := volume) hφ φ.compact e
  have hd (x : SpatialCoordinates d) : lineDeriv ℝ φ.value x (-e) = -(fderiv ℝ φ.value x e) := by
    rw [((φ.smooth.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv,map_neg]
  simp_rw [hd,neg_mul] at hi
  rw [integral_neg] at hi
  have huI : (∫ x, fderiv ℝ φ.value x e*u x) = ∫ x, fderiv ℝ φ.value x e*f x :=
    integral_congr_ae (hu.mono fun _ hx => by dsimp only; rw [hx])
  have hvI : (∫ x, φ.value x*v x) = ∫ x, lineDeriv ℝ f x e*φ.value x :=
    integral_congr_ae (hv.mono fun _ hx => by dsimp only at hx ⊢; rw [hx,mul_comm])
  rw [huI,hvI]
  linarith

def lipschitzGlobalJet {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume : Measure (SpatialCoordinates d)))
    (hu : u =ᵐ[volume] f) (hA : ∀ᵐ x ∂volume, HasFDerivAt f (A x) x) :
    WeakSobolevJet d 1 volume Set.univ := by
  apply firstOrderJet u A
  intro i
  apply weakSpatialDerivative_of_lipschitz_full hf _ _ _ hu
  filter_upwards [OperatorMultiplier.const_map_ae
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) A,hA] with x hx hAx
  exact hx.trans (hAx.hasLineDerivAt _).lineDeriv.symm

theorem lipschitzGlobalJet_value {f : SpatialCoordinates d → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume : Measure (SpatialCoordinates d)))
    (hu : u =ᵐ[volume] f) (hA : ∀ᵐ x ∂volume, HasFDerivAt f (A x) x) :
    WeakSobolevJet.value (lipschitzGlobalJet hf u A hu hA) = u := firstOrderJet_value _ _ _

end Carleman
