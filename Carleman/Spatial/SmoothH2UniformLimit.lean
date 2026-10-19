module

public import Carleman.Spatial.TensorCoordinateL2
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Strong convergence of the finitely many actual H² components yields a
uniformly Cauchy sequence and a continuous limit on the same convex compact
set. No pointwise convergence assumption is added. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {K : Set (SpatialCoordinates d)}

theorem coordinateDerivative_sub {k : ℕ} (v : Fin k → Fin d)
    {f g : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    coordinateDerivative v (f-g) = fun x => coordinateDerivative v f x-coordinateDerivative v g x := by
  funext x
  unfold coordinateDerivative
  rw [iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt,map_sub]

theorem bochnerL2Norm_sub_le_errors {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g a : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (ha : MemLp a 2 μ) :
    bochnerL2Norm μ (f-g) ≤ bochnerL2Norm μ (f-a)+bochnerL2Norm μ (g-a) := by
  have he : f-g=(f-a)-(g-a) := by funext x; simp only [Pi.sub_apply]; ring
  rw [he]
  exact bochnerL2Norm_sub (hf.sub ha) (hg.sub ha)

set_option maxHeartbeats 1200000 in
theorem convex_smooth_h2_uniform_limit
    (hK : IsCompact K) (hc : Convex ℝ K) (hvol : 0 < volume.real K) (hd : d ≤ 3)
    {F : ℕ → SpatialCoordinates d → ℝ} (hF : ∀ n, ContDiff ℝ 2 (F n))
    {a : SpatialCoordinates d → ℝ} {b : (Fin 1 → Fin d) → SpatialCoordinates d → ℝ}
    {c : (Fin 2 → Fin d) → SpatialCoordinates d → ℝ}
    (ha : MemLp a 2 (volume.restrict K)) (hb : ∀ v, MemLp (b v) 2 (volume.restrict K))
    (hc₂ : ∀ v, MemLp (c v) 2 (volume.restrict K))
    (ht₀ : Tendsto (fun n => bochnerL2Norm (volume.restrict K) (F n-a)) atTop (𝓝 0))
    (ht₁ : ∀ v, Tendsto (fun n => bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-b v)) atTop (𝓝 0))
    (ht₂ : ∀ v, Tendsto (fun n => bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-c v)) atTop (𝓝 0))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f K ∧ TendstoUniformlyOn F f atTop K := by
  let B := Real.sqrt (volume.real K)/volume.real K
  let C₁ := D*tensorCoordinateBound d 1
  let C₂ := 2*D^2*tensorCoordinateBound d 2
  let E := fun n => bochnerL2Norm (volume.restrict K) (F n-a)+
    C₁*(∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-b v))+
    C₂*(∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-c v))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC₁ : 0 ≤ C₁ := mul_nonneg hD tensorCoordinateBound_pos.le
  have hC₂ : 0 ≤ C₂ := mul_nonneg (by positivity) tensorCoordinateBound_pos.le
  have hE : Tendsto E atTop (𝓝 0) := by
    have h₁ := tendsto_finsetSum Finset.univ (fun v _ => ht₁ v)
    have h₂ := tendsto_finsetSum Finset.univ (fun v _ => ht₂ v)
    simpa only [Finset.sum_const_zero,mul_zero,add_zero,E] using
      (ht₀.add (h₁.const_mul C₁)).add (h₂.const_mul C₂)
  have hcm (k : ℕ) (hk : k ≤ 2) (v : Fin k → Fin d) (n : ℕ) :
      MemLp (coordinateDerivative v (F n)) 2 (volume.restrict K) :=
    continuous_memLp_compact hK ((coordinateTensorEval v).continuous.comp
      ((hF n).continuous_iteratedFDeriv (by exact_mod_cast hk)))
  have hpoint (m n : ℕ) (x : SpatialCoordinates d) (hx : x ∈ K) :
      |F m x-F n x| ≤ B*(E m+E n) := by
    have hp := convex_smooth_h2_coordinate_point_bound hK hc hvol hd ((hF m).sub (hF n)) hD hdiam hx
    change |F m x-F n x| ≤ B*(bochnerL2Norm (volume.restrict K) (F m-F n)+
      C₁*(∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m-F n)))+
      C₂*(∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m-F n)))) at hp
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ hB
    have h₀ := bochnerL2Norm_sub_le_errors (continuous_memLp_compact hK (hF m).continuous)
      (continuous_memLp_compact hK (hF n).continuous) ha
    have hs₁ : (∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m-F n))) ≤
        (∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m)-b v))+
        (∑ v : Fin 1 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-b v)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro v _
      rw [coordinateDerivative_sub v ((hF m).of_le (by norm_num)) ((hF n).of_le (by norm_num))]
      exact bochnerL2Norm_sub_le_errors (hcm 1 (by omega) v m) (hcm 1 (by omega) v n) (hb v)
    have hs₂ : (∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m-F n))) ≤
        (∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F m)-c v))+
        (∑ v : Fin 2 → Fin d, bochnerL2Norm (volume.restrict K) (coordinateDerivative v (F n)-c v)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro v _
      rw [coordinateDerivative_sub v (hF m) (hF n)]
      exact bochnerL2Norm_sub_le_errors (hcm 2 le_rfl v m) (hcm 2 le_rfl v n) (hc₂ v)
    dsimp only [E]
    nlinarith only [h₀,mul_le_mul_of_nonneg_left hs₁ hC₁,mul_le_mul_of_nonneg_left hs₂ hC₂]
  have huc : UniformCauchySeqOn F atTop K := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have ht : Tendsto (fun n => B*E n) atTop (𝓝 0) := by simpa only [mul_zero] using hE.const_mul B
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,fun m hm n hn x hx => ?_⟩
    rw [Real.dist_eq]
    have hpm := hN m hm
    have hpn := hN n hn
    exact (hpoint m n x hx).trans_lt (by nlinarith only [hpm,hpn])
  have hex (x : SpatialCoordinates d) : ∃ y : ℝ, x ∈ K → Tendsto (fun n => F n x) atTop (𝓝 y) := by
    by_cases hx : x ∈ K
    · obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete (huc.cauchySeq hx)
      exact ⟨y,fun _ => hy⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose f hf using hex
  have hu := huc.tendstoUniformlyOn_of_tendsto hf
  exact ⟨f,hu.continuousOn (Filter.Frequently.of_forall fun n => (hF n).continuous.continuousOn),hu⟩

end Carleman
