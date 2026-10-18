module

public import Carleman.Spatial.SubdomainRestriction
public import Carleman.Spatial.LipschitzWeakDerivative
public import Carleman.Spatial.FirstOrderSobolevJet
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-! The genuine weak gradient of an affine L² representative is its
actual affine derivative. This applies to every weak H¹ state locally. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ} (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)

def affineScalarDerivative : SpatialCoordinates d →L[ℝ] ℝ :=
  (⟨p,p.continuous_of_finiteDimensional⟩ : SpatialCoordinates d →ᴬ[ℝ] ℝ).contLinear

theorem affineScalar_hasFDerivAt (x : SpatialCoordinates d) :
    HasFDerivAt p (affineScalarDerivative p) x :=
  (⟨p,p.continuous_of_finiteDimensional⟩ : SpatialCoordinates d →ᴬ[ℝ] ℝ).hasFDerivAt

theorem affineScalar_lipschitz : LipschitzWith ‖affineScalarDerivative p‖₊ p := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have he : p x-p y = affineScalarDerivative p (x-y) := (p.linear_apply_vsub x y).symm
  rw [he]
  exact (affineScalarDerivative p).le_opNorm (x-y)

theorem weakDerivative_eq_affine {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    [IsFiniteMeasure (volume.restrict S)] (e : SpatialCoordinates d)
    (u v : Lp ℝ 2 (volume.restrict S))
    (hu : u =ᵐ[volume.restrict S] p)
    (hw : IsWeakSpatialDerivative (volume.restrict S) S e u v) :
    v =ᵐ[volume.restrict S] (fun x => fderiv ℝ p x e) := by
  let c := affineScalarDerivative p e
  let w : Lp ℝ 2 (volume.restrict S) := (memLp_const c (p := 2) (μ := volume.restrict S)).toLp (fun _ => c)
  have hc : w =ᵐ[volume.restrict S] (fun _ => c) := MemLp.coeFn_toLp _
  have hw' : IsWeakSpatialDerivative (volume.restrict S) S e u w := by
    apply weakSpatialDerivative_of_lipschitz (affineScalar_lipschitz p) e u w hu
    filter_upwards [hc] with x hx
    rw [hx,((affineScalar_hasFDerivAt p x).hasLineDerivAt e).lineDeriv]
  have he := hw.unique hS (ae_restrict_mem hS.measurableSet) hw'
  rw [he]
  filter_upwards [hc] with x hx
  rw [hx,(affineScalar_hasFDerivAt p x).fderiv]

theorem WeakSobolevJet.gradient_eq_affine {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    [IsFiniteMeasure (volume.restrict S)]
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u =ᵐ[volume.restrict S] p) :
    WeakSobolevJet.field 1 u =ᵐ[volume.restrict S] (fun x => derivativeOneFiber (fderiv ℝ p x)) := by
  have hc (i : Fin d) : ∀ᵐ x ∂volume.restrict S,
      WeakSobolevJet.field 1 u x (Sym.oneEquiv i) =
        fderiv ℝ p x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    have hw : IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i)
        (WeakSobolevJet.value u) (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) :=
      WeakSobolevJet.field_weak_derivative u 0 Sym.nil i
    have he := weakDerivative_eq_affine p hS (EuclideanSpace.basisFun (Fin d) ℝ i) _ _ hu hw
    filter_upwards [he,derivativeComponent_ae (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)] with x hx hd
    exact hd.symm.trans hx
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext α
  change WeakSobolevJet.field 1 u x α = fderiv ℝ p x (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm α))
  simpa only [Equiv.apply_symm_apply] using hx (Sym.oneEquiv.symm α)

end Carleman
