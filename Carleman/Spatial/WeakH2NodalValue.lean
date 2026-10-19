module

public import Carleman.Spatial.WeakH2NodalSmoothing
public import Carleman.Spatial.SimplexH2ValueLimit
public import Carleman.Spatial.DirichletZeroExtension

/-! The actual local nodal value estimate for every original weak H² state.
The right side is the original local Hessian field, not its whole-domain norm. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem derivativeComponent_local_integral_le {k : ℕ} (K : Set (SpatialCoordinates d))
    (α : Sym (Fin d) k) (w : Lp (DerivativeFiber d k) 2 (volume : Measure (SpatialCoordinates d))) :
    (∫ x in K, (derivativeComponent α w x)^2) ≤ ∫ x in K, ‖w x‖^2 := by
  apply integral_mono_ae ((Lp.memLp (derivativeComponent α w)).restrict K).integrable_sq
    ((Lp.memLp w).restrict K).norm.integrable_sq
  filter_upwards [(derivativeComponent_ae α w).filter_mono (ae_mono Measure.restrict_le_self)] with x hx
  rw [hx]
  have h := (sq_le_sq₀ (norm_nonneg (w x α)) (norm_nonneg (w x))).mpr (PiLp.norm_apply_le (w x) α)
  simpa only [Real.norm_eq_abs,sq_abs] using h

theorem WeakSobolevJet.simplex_nodal_value_integral
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (closure S))
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u)
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hKS : simplicialCell T.points ⊆ closure S)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∫ x in simplicialCell T.points, (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
      16*D^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*
        (∫ x in simplicialCell T.points, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2) := by
  have hne : (closure S).Nonempty :=
    ⟨T.points 0,hKS (subset_convexHull ℝ _ (mem_range_self 0))⟩
  obtain ⟨a,ha⟩ := closure_nonempty_iff.mp hne
  obtain ⟨F,hF,hl,_,_,ht₂⟩ := WeakSobolevJet.exists_smooth_h2_pointwise_approximation hS hc hb hd ha u hf hfu
  let K := simplicialCell T.points
  let Z := fun v : Fin 2 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u))
  have hK : IsCompact K := simplicialCell_compact T.points
  have ht (v : Fin 2 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => coordinateDerivative v (F n) x-Z v x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ (ht₂ v)
    intro n
    have hm : MemLp (fun x => coordinateDerivative v (F n) x-Z v x) 2
        (volume.restrict (closure S)) :=
      (continuous_memLp_compact (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
        ((coordinateTensorEval v).continuous.comp ((hF n).continuous_iteratedFDeriv (by simp)))).sub
        ((Lp.memLp (Z v)).restrict (closure S))
    exact ENNReal.toReal_mono hm.ne (eLpNorm_mono_measure _ (Measure.restrict_mono hKS le_rfl))
  have he := simplexNodal_h2_value_integral_of_limit T hd (hf.mono hKS)
    (fun n => (hF n).of_le (by simp)) (fun x hx => hl x (hKS hx))
    (fun v => (Lp.memLp (Z v)).restrict K) ht hD hdiam
  have hsum : (∑ v : Fin 2 → Fin d, ∫ x in K, (Z v x)^2) ≤
      (d:ℝ)^2*(∫ x in K, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2) := by
    calc
      _ ≤ ∑ _v : Fin 2 → Fin d, ∫ x in K,
          ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2 := by
        apply Finset.sum_le_sum
        intro v _
        dsimp only [Z]
        rw [← derivativeComponent_zeroExtend]
        exact derivativeComponent_local_integral_le K _ _
      _ = _ := by simp
  exact he.trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring))

theorem WeakSobolevJet.exists_nodal_value_representative
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f (closure S) ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      ∀ T : Affine.Simplex ℝ (SpatialCoordinates d) d,
        simplicialCell T.points ⊆ closure S → ∀ D : ℝ, 0 ≤ D →
        (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) →
        (∫ x in simplicialCell T.points, (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
          16*D^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*
            (∫ x in simplicialCell T.points, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2) := by
  obtain ⟨f,hf,hu⟩ := WeakSobolevJet.exists_closure_continuous_representative hS hc hb hd u
  exact ⟨f,hf,hu,fun T hT _ hD hdiam =>
    WeakSobolevJet.simplex_nodal_value_integral hS hc hb hd u hf hu T hT hD hdiam⟩

end Carleman
