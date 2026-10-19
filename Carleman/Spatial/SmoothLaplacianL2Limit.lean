module

public import Carleman.Spatial.BoxCompactSmoothDensity
public import Carleman.Spatial.WeakDerivativeStrongLimit
public import Carleman.Spatial.SmoothLaplacianProduct

/-! Componentwise strong limits give the actual L2 Laplacian graph limit. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem lp_tendsto_of_representative_L2_error {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (F : ℕ → X → ℝ)
    (he : ∀ n, u n =ᵐ[μ] F n)
    (ht : Tendsto (fun n => bochnerL2Norm μ (fun x => F n x-v x)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  change bochnerL2Norm μ (fun x => F n x-v x)=‖u n-v‖
  have hn : bochnerL2Norm μ (u n-v)=‖u n-v‖ := by
    rw [bochnerL2Norm_eq _ (Lp.memLp (u n-v)),Lp.toLp_coeFn]
  rw [← hn]
  apply bochnerL2Norm_congr_ae
  filter_upwards [Lp.coeFn_sub (u n) v,he n] with x hx hy
  rw [hx,Pi.sub_apply,hy]

theorem coordinateDerivative_two_diagonal {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin d) (x : SpatialCoordinates d) :
    coordinateDerivative ![i,i] f x=
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
        (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [coordinateDerivative_two,iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he := fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const (EuclideanSpace.basisFun (Fin d) ℝ i))
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add] at he
  exact (congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A (EuclideanSpace.basisFun (Fin d) ℝ i)) he).symm

namespace SpatialTest
variable {S : Set (SpatialCoordinates d)}

def laplacianOnLp (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) : Lp ℝ 2 (volume.restrict S) :=
  ∑ i : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem laplacianOnLp_ae (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) :
    φ.laplacianOnLp S =ᵐ[volume.restrict S] spatialLaplacian φ.value := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin d =>
    (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
      (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)),
    ae_all_iff.mpr (fun i : Fin d =>
      (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp_ae
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))] with x hx hd
  change (∑ i : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) x = _
  rw [hx]
  exact Finset.sum_congr rfl (fun i _ => hd i)

theorem laplacianOnLp_tendsto (U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)))
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (ht : ∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => coordinateDerivative v (U n).value x-
        derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u) x))
      atTop (𝓝 0)) :
    Tendsto (fun n => -(U n).laplacianOnLp S) atTop (𝓝 (negativeLaplacian u)) := by
  have hc (i : Fin d) : Tendsto (fun n =>
      ((U n).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))
      atTop (𝓝 (derivativeComponent (Sym.cons i (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 u))) := by
    apply lp_tendsto_of_representative_L2_error _ _ (fun n => coordinateDerivative ![i,i] (U n).value) _
      (by simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using ht ![i,i])
    intro n
    filter_upwards [((U n).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp_ae
      (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)] with x hx
    rw [hx,coordinateDerivative_two_diagonal (U n).smooth]
    rfl
  rw [negativeLaplacian_apply]
  exact (tendsto_finsetSum Finset.univ (fun i _ => hc i)).neg

end SpatialTest
end Carleman
