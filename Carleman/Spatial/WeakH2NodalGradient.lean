module

public import Carleman.Spatial.WeakH2NodalValue
public import Carleman.Spatial.SimplexH2GradientLimit

/-! Local nodal gradient errors for all original weak H² states. The full
weak gradient and Hessian are retained on the same physical simplex. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem derivativeOneFiber_local_sub_integral_eq
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K)
    (w : Lp (DerivativeFiber d 1) 2 (volume : Measure (SpatialCoordinates d)))
    (A : SpatialCoordinates d →L[ℝ] ℝ) :
    (∫ x in K, ‖w x-derivativeOneFiber A‖^2) =
      ∑ i : Fin d, ∫ x in K,
        (derivativeComponent (Sym.cons i Sym.nil) w x-A (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_ne_top.lt_top⟩
  have he : ∀ᵐ x ∂volume.restrict K, ∀ i : Fin d,
      derivativeComponent (Sym.cons i Sym.nil) w x=w x (Sym.cons i Sym.nil) :=
    ae_all_iff.mpr fun i => (derivativeComponent_ae _ w).filter_mono (ae_mono Measure.restrict_le_self)
  calc
    _ = ∫ x in K, ∑ i : Fin d,
        (derivativeComponent (Sym.cons i Sym.nil) w x-A (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      simp only [firstDerivativeFiber_sub_norm_sq,hx]
    _ = _ := integral_finsetSum _ (fun i _ =>
      (((Lp.memLp (derivativeComponent (Sym.cons i Sym.nil) w)).restrict K).sub (memLp_const _)).integrable_sq)

set_option maxHeartbeats 1200000 in
theorem WeakSobolevJet.simplex_nodal_gradient_integral
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (closure S))
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u)
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hKS : simplicialCell T.points ⊆ closure S)
    {a : SpatialCoordinates d} {r D κ : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : D ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    (∫ x in simplicialCell T.points,
      ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field ⟨1,by omega⟩ u) x-
        derivativeOneFiber (affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i))))‖^2) ≤
      ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
        (tensorCoordinateBound d 2)^2*(d:ℝ)^2*
          (∫ x in simplicialCell T.points, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2) := by
  have hne : (closure S).Nonempty :=
    ⟨T.points 0,hKS (subset_convexHull ℝ _ (mem_range_self 0))⟩
  obtain ⟨b,hbS⟩ := closure_nonempty_iff.mp hne
  obtain ⟨F,hF,hl,_,ht₁,ht₂⟩ := WeakSobolevJet.exists_smooth_h2_pointwise_approximation hS hc hb hd hbS u hf hfu
  let K := simplicialCell T.points
  have hK : IsCompact K := simplicialCell_compact T.points
  have hclosed : IsCompact (closure S) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  let G := fun i : Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field ⟨1,by omega⟩ u))
  let Z := fun v : Fin 2 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u))
  have hrestrict (g : ℕ → SpatialCoordinates d → ℝ) (hg : ∀ n, Continuous (g n))
      (w : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
      (ht : Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S)) (fun x => g n x-w x)) atTop (𝓝 0)) :
      Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x => g n x-w x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ ht
    intro n
    have hm := (continuous_memLp_compact hclosed (hg n)).sub ((Lp.memLp w).restrict (closure S))
    exact ENNReal.toReal_mono hm.ne (eLpNorm_mono_measure _ (Measure.restrict_mono hKS le_rfl))
  have hg (i : Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => fderiv ℝ (F n) x (EuclideanSpace.basisFun (Fin d) ℝ i)-G i x)) atTop (𝓝 0) := by
    have ht := ht₁ (fun _ => i)
    simp only [coordinateDerivative_one] at ht
    exact hrestrict _ (fun n => ((hF n).continuous_fderiv (by simp)).clm_apply continuous_const) (G i) ht
  have hz (v : Fin 2 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict K)
      (fun x => coordinateDerivative v (F n) x-Z v x)) atTop (𝓝 0) :=
    hrestrict _ (fun n => (coordinateTensorEval v).continuous.comp
      ((hF n).continuous_iteratedFDeriv (by simp))) (Z v) (ht₂ v)
  have he := simplexNodal_h2_gradient_integral_of_limit T hd
    (fun n => (hF n).of_le (by simp)) (fun i => hl _ (hKS (subset_convexHull ℝ _ (mem_range_self i))))
    (fun i => (Lp.memLp (G i)).restrict K) hg (fun v => (Lp.memLp (Z v)).restrict K) hz
    hr hD hball hshape hdiam
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
  rw [derivativeOneFiber_local_sub_integral_eq hK]
  simp only [derivativeComponent_zeroExtend]
  exact he.trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring))

set_option maxHeartbeats 1200000 in
theorem WeakSobolevJet.exists_nodal_h2_representative
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f (closure S) ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      ∀ T : Affine.Simplex ℝ (SpatialCoordinates d) d,
        simplicialCell T.points ⊆ closure S → ∀ (a : SpatialCoordinates d) (r D κ : ℝ),
        0 < r → 0 ≤ D → (Metric.ball a r ⊆ simplicialCell T.points) → D ≤ κ*r →
        (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) →
        ((∫ x in simplicialCell T.points, (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
          16*D^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*
            (∫ x in simplicialCell T.points, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2)) ∧
        ((∫ x in simplicialCell T.points,
          ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field ⟨1,by omega⟩ u) x-
            derivativeOneFiber (affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i))))‖^2) ≤
          ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
            (tensorCoordinateBound d 2)^2*(d:ℝ)^2*
              (∫ x in simplicialCell T.points, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2)) := by
  obtain ⟨f,hf,hu⟩ := WeakSobolevJet.exists_closure_continuous_representative hS hc hb hd u
  refine ⟨f,hf,hu,?_⟩
  intro T hT a r D κ hr hD hball hshape hdiam
  exact ⟨WeakSobolevJet.simplex_nodal_value_integral hS hc hb hd u hf hu T hT hD hdiam,
    WeakSobolevJet.simplex_nodal_gradient_integral hS hc hb hd u hf hu T hT hr hD hball hshape hdiam⟩

end Carleman
