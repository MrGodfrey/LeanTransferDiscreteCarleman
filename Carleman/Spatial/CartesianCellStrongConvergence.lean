module

public import Carleman.Spatial.FixedBoxCellReconstruction
public import Carleman.Spatial.DenseReconstructionConvergence
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Strong L² consistency of the original interior dual-cell averages for arbitrary L² data. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianBoxCell_continuous_residual_tendsto (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (f : SpatialCoordinates d →ᵇ ℝ) :
    let ν := volume.restrict (openCoordinateBox lo hi)
    let u := BoundedContinuousFunction.toLp 2 ν ℝ f
    Tendsto (fun n => ‖u-cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      ((cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)).toContinuousLinearMap.adjoint u)‖)
      atTop (𝓝 0) := by
  dsimp only
  let ν := volume.restrict (openCoordinateBox lo hi)
  let V := ν.real univ
  have hV : 0 ≤ V := measureReal_nonneg
  have hδlim j : Tendsto (fun n => δ n j) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hδ n j).le) (fun n => hstep n j) hlim
  have hstrip := cartesianBox_uncovered_volume_tendsto lo hi δ hδ N hN hbox hδlim
  have hweighted := (tendsto_const_nhds (x := ‖f‖^2)).mul hstrip
  have hcompact := (openCoordinateBox_isBounded lo hi).isCompact_closure
  have huc := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous f.continuous.continuousOn)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := Real.sqrt (ε^2/(2*(V+1)))
  have hη : 0 < η := Real.sqrt_pos.mpr (div_pos (sq_pos_of_pos hε) (by positivity))
  have hηeq : η^2*(2*(V+1))=ε^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ε^2/(2*(V+1)))]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨r,hr,hrf⟩ := huc η hη
  have hdist : Tendsto (fun n => (d:ℝ)*h n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (d:ℝ))).mul hlim
  have hbsmall : ∀ᶠ n in atTop, ‖f‖^2*ν.real
      (⋃ a : CartesianInteriorIndex (N n), cartesianDualCell lo (δ n) (N n) a)ᶜ < ε^2/2 := by
    have hzero : (‖f‖^2)*0=(0:ℝ) := mul_zero _
    rw [hzero] at hweighted
    exact hweighted.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hdist.eventually (gt_mem_nhds hr),hbsmall] with n hdn hbn
  have hloc : ∀ a : CartesianInteriorIndex (N n), ∀ x ∈ cartesianDualCell lo (δ n) (N n) a,
      |f x-f (cartesianInteriorPoint lo (δ n) (N n) a)| ≤ η := by
    intro a x hx
    have hcell := cartesianDualCell_subset lo (δ n) (hδ n) (N n) a hx
    have hnode := cartesianInteriorPoint_mem lo (δ n) (hδ n) (N n) a
    rw [funext (hbox n)] at hcell hnode
    have he := hrf x (subset_closure hcell) _ (subset_closure hnode)
      ((cartesianDualCell_dist_le lo (δ n) (hδ n) (N n) (hh n) (hstep n) a hx).trans_lt hdn)
    exact (show |f x-f (cartesianInteriorPoint lo (δ n) (N n) a)| < η from he).le
  have he := cartesianBoxCell_average_error lo hi (δ n) (hδ n) (N n) (hbox n) f hη.le hloc
  dsimp only at he
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  have hvbound : η^2*V ≤ ε^2/2 := by nlinarith [sq_nonneg η]
  have hsq : ‖BoundedContinuousFunction.toLp 2 ν ℝ f-
      cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
        ((cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)).toContinuousLinearMap.adjoint
          (BoundedContinuousFunction.toLp 2 ν ℝ f))‖^2 < ε^2 := by
    change _ ≤ η^2*V+‖f‖^2*ν.real _ at he
    linarith
  nlinarith [norm_nonneg (BoundedContinuousFunction.toLp 2 ν ℝ f-
    cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      ((cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)).toContinuousLinearMap.adjoint
        (BoundedContinuousFunction.toLp 2 ν ℝ f)))]

theorem cartesianBoxCell_average_strong_convergence (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) :
    Tendsto (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      ((cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)).toContinuousLinearMap.adjoint u))
      atTop (𝓝 u) := by
  apply isometric_reconstruction_tendsto_of_denseRange
    (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n))
    (BoundedContinuousFunction.toLp 2 (volume.restrict (openCoordinateBox lo hi)) ℝ)
    (BoundedContinuousFunction.toLp_denseRange ℝ (volume.restrict (openCoordinateBox lo hi)) ℝ (by norm_num))
  exact cartesianBoxCell_continuous_residual_tendsto lo hi δ hδ N hN hbox h hh hstep hlim

end Carleman
