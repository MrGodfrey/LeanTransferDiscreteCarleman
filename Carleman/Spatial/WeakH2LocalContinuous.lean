module

public import Carleman.Spatial.SmoothH2UniformLimit
public import Carleman.Spatial.WeakH2LocalSmoothing

/-! A genuine continuous representative of every weak H² state on any
positive-volume convex compact subset of the original open domain, obtained
as a uniform limit of the same actual local mollifications. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem coordinateDerivative_one (v : Fin 1 → Fin d) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    coordinateDerivative v f x = fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ (v 0)) := by
  change iteratedFDeriv ℝ 1 f x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (v i)) = _
  rw [iteratedFDeriv_one_apply]

theorem coordinateDerivative_two (v : Fin 2 → Fin d) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    coordinateDerivative v f x = iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.basisFun (Fin d) ℝ (v 0),EuclideanSpace.basisFun (Fin d) ℝ (v 1)] := by
  change iteratedFDeriv ℝ 2 f x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (v i)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem WeakSobolevJet.exists_local_continuous_representative
    (hS : IsOpen S) (hK : IsCompact K) (hc : Convex ℝ K) (hKS : K ⊆ S)
    (hvol : 0 < volume.real K) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    let U := fun n => zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d n).value
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f K ∧
      f =ᵐ[volume.restrict K] WeakSobolevJet.value u ∧ TendstoUniformlyOn U f atTop K := by
  intro U
  have hs := WeakSobolevJet.local_mollification_strong_h2 hS hK hKS u
  let b := fun v : Fin 1 → Fin d =>
    derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u)
  let c := fun v : Fin 2 → Fin d =>
    derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u)
  have hμ : volume.restrict K ≤ volume.restrict S := Measure.restrict_mono hKS le_rfl
  have h₁ (v : Fin 1 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => coordinateDerivative v (U n) x-b v x)) atTop (𝓝 0) := by
    simpa only [coordinateDerivative_one,b,U] using hs.2.2.1 (v 0)
  have h₂ (v : Fin 2 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => coordinateDerivative v (U n) x-c v x)) atTop (𝓝 0) := by
    simpa only [coordinateDerivative_two,c,U] using hs.2.2.2 (v 0) (v 1)
  obtain ⟨f,hf,hu⟩ := convex_smooth_h2_uniform_limit hK hc hvol hd
    (fun n => (hs.1 n).of_le (by simp)) ((Lp.memLp (WeakSobolevJet.value u)).mono_measure hμ)
    (fun v => (Lp.memLp (b v)).mono_measure hμ) (fun v => (Lp.memLp (c v)).mono_measure hμ)
    hs.2.1 h₁ h₂ hD hdiam
  refine ⟨f,hf,?_,hu⟩
  filter_upwards [(spatialMollifier_converges (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))).filter_mono
    (ae_mono Measure.restrict_le_self),ae_restrict_mem hK.measurableSet,
    (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.value u)).filter_mono (ae_mono hμ)] with x hx hxK hxe
  exact (tendsto_nhds_unique (hu.tendsto_at hxK) hx).trans hxe

end Carleman
