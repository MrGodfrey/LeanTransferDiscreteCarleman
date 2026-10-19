module

public import Carleman.Spatial.FiniteCellApproximation
public import Carleman.Spatial.DenseReconstructionConvergence
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Actual cell averages converge strongly when their diameter and uncovered measure vanish. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology
namespace Carleman
variable {Ω : Type*} [MetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {ν : Measure Ω} [IsFiniteMeasure ν] [ν.WeaklyRegular]
  {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
  (K : ∀ n, ι n → Set Ω) (hK : ∀ n i, MeasurableSet (K n i))
  (mass : ℕ → ℝ) (hm : ∀ n, 0 < mass n)
  (hdis : ∀ n, Pairwise fun i j => Disjoint (K n i) (K n j))
  (hvol : ∀ n i, ν.real (K n i)=mass n)
  (A : Set Ω) (hA : IsCompact A) (p : ∀ n, ι n → Ω)
  (hp : ∀ n i, p n i ∈ A) (hinc : ∀ n i, K n i ⊆ A)
  (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
  (hdist : ∀ n i x, x ∈ K n i → dist x (p n i) ≤ r n)
  (hstrip : Tendsto (fun n => ν.real (⋃ i, K n i)ᶜ) atTop (𝓝 0))

include hA hp hinc hr hdist hstrip in
omit [ν.WeaklyRegular] in
theorem finiteCell_continuous_residual_tendsto (f : Ω →ᵇ ℝ) :
    let u := BoundedContinuousFunction.toLp 2 ν ℝ f
    Tendsto (fun n => ‖u-finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)
      ((finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)).toContinuousLinearMap.adjoint u)‖)
      atTop (𝓝 0) := by
  dsimp only
  let u := BoundedContinuousFunction.toLp 2 ν ℝ f
  let V := ν.real univ
  have hV : 0 ≤ V := measureReal_nonneg
  have huc := Metric.uniformContinuousOn_iff.mp (hA.uniformContinuousOn_of_continuous f.continuous.continuousOn)
  have hweighted := (tendsto_const_nhds (x := ‖f‖^2)).mul hstrip
  rw [mul_zero] at hweighted
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := Real.sqrt (ε^2/(2*(V+1)))
  have hη : 0 < η := Real.sqrt_pos.mpr (div_pos (sq_pos_of_pos hε) (by positivity))
  have hηeq : η^2*(2*(V+1))=ε^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ε^2/(2*(V+1)))]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨s,hs,hsf⟩ := huc η hη
  filter_upwards [hr.eventually (gt_mem_nhds hs),
    hweighted.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε^2/2))] with n hrn hbn
  have hlocal : ∀ i, ∀ᵐ x ∂ν, x ∈ K n i → |u x-f (p n i)| ≤ η := by
    intro i
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 ν ℝ f] with x hx
    intro hxi
    rw [show u x=f x from hx]
    exact (hsf x (hinc n i hxi) (p n i) (hp n i) ((hdist n i x hxi).trans_lt hrn)).le
  have hbound : ∀ᵐ x ∂ν, |u x| ≤ ‖f‖ := by
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 ν ℝ f] with x hx
    rw [show u x=f x from hx]
    exact f.norm_coe_le_norm x
  have he := finiteCell_average_error_bound (K n) (hK n) (hm n) (hdis n) (hvol n)
    (fun i => f (p n i)) u hη.le (norm_nonneg f) hlocal hbound
  have hvbound : η^2*V ≤ ε^2/2 := by nlinarith [sq_nonneg η]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  change ‖u-finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)
    ((finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)).toContinuousLinearMap.adjoint u)‖ < ε
  change _ ≤ η^2*V+_ at he
  nlinarith [norm_nonneg (u-finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)
    ((finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)).toContinuousLinearMap.adjoint u))]

include hA hp hinc hr hdist hstrip in
theorem finiteCell_average_strong_convergence (u : Lp ℝ 2 ν) :
    Tendsto (fun n => finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)
      ((finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n)).toContinuousLinearMap.adjoint u))
      atTop (𝓝 u) := by
  apply isometric_reconstruction_tendsto_of_denseRange
    (fun n => finiteCellIsometry (K n) (hK n) (hm n) (hdis n) (hvol n))
    (BoundedContinuousFunction.toLp 2 ν ℝ)
    (BoundedContinuousFunction.toLp_denseRange ℝ ν ℝ (by norm_num))
  exact finiteCell_continuous_residual_tendsto K hK mass hm hdis hvol A hA p hp hinc r hr hdist hstrip

end Carleman
