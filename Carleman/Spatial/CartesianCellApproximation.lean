module

public import Carleman.Spatial.FiniteCellApproximation
public import Carleman.Spatial.CartesianCellControlSupport
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Quantitative approximation by the original Cartesian cell averages, with the true boundary strip. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction NNReal
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianDualCells_union_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) :
    (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))).real
      (⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a)=
        ∏ j, ((N j-1:ℕ):ℝ)*δ j := by
  rw [finiteCells_union_volume (cartesianDualCell o δ N) (cartesianDualCell_measurable o δ N)
    (cartesianDualCell_disjoint o δ hδ N) (cartesianDualCell_restrict_volume o δ hδ N)]
  simp only [CartesianInteriorIndex,Fintype.card_pi,Fintype.card_fin,Nat.cast_prod,
    Finset.prod_mul_distrib]

theorem cartesianDualCells_uncovered_volume (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hN : ∀ j, 0 < N j) :
    (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))).real
      (⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a)ᶜ=
        (∏ j, (N j:ℝ)*δ j)-(∏ j, ((N j:ℝ)*δ j-δ j)) := by
  rw [measureReal_compl (MeasurableSet.iUnion (cartesianDualCell_measurable o δ N)),
    cartesianDualCells_union_volume o δ hδ N]
  have hfull : (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))).real univ=
      ∏ j, (N j:ℝ)*δ j := by
    simp only [Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rw [← Measure.real,openCoordinateBox_volume_real _ _ (fun j => by
      have : (0:ℝ)<N j := by exact_mod_cast hN j
      linarith [mul_pos this (hδ j)])]
    simp only [add_sub_cancel_left]
  rw [hfull]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Nat.cast_sub (hN j : 1 ≤ N j),Nat.cast_one]
  ring

theorem cartesianCell_average_continuous_error (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d →ᵇ ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hloc : ∀ a : CartesianInteriorIndex N, ∀ x ∈ cartesianDualCell o δ N a,
      |f x-f (cartesianInteriorPoint o δ N a)| ≤ ε) :
    let ν := volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    let u := BoundedContinuousFunction.toLp 2 ν ℝ f
    let E := cartesianCellIsometry o δ hδ N
    ‖u-E (E.toContinuousLinearMap.adjoint u)‖^2 ≤
      ε^2*ν.real univ+‖f‖^2*ν.real (⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a)ᶜ := by
  dsimp only
  let ν := volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  let u := BoundedContinuousFunction.toLp 2 ν ℝ f
  apply finiteCell_average_error_bound (cartesianDualCell o δ N) (cartesianDualCell_measurable o δ N)
    (Finset.prod_pos (fun j _ => hδ j)) (cartesianDualCell_disjoint o δ hδ N)
    (cartesianDualCell_restrict_volume o δ hδ N)
    (fun a => f (cartesianInteriorPoint o δ N a)) u hε (norm_nonneg f)
  · intro a
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 ν ℝ f] with x hx
    intro hxa
    rw [hx]
    exact hloc a x hxa
  · filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 ν ℝ f] with x hx
    rw [hx]
    exact f.norm_coe_le_norm x

theorem cartesianCell_average_lipschitz_error (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d →ᵇ ℝ) {C : ℝ≥0} (hf : LipschitzWith C f)
    {h : ℝ} (hh : 0 ≤ h) (hstep : ∀ j, δ j ≤ h) :
    let ν := volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    let u := BoundedContinuousFunction.toLp 2 ν ℝ f
    let E := cartesianCellIsometry o δ hδ N
    ‖u-E (E.toContinuousLinearMap.adjoint u)‖^2 ≤
      ((C:ℝ)*(d:ℝ)*h)^2*ν.real univ+
        ‖f‖^2*ν.real (⋃ a : CartesianInteriorIndex N, cartesianDualCell o δ N a)ᶜ := by
  apply cartesianCell_average_continuous_error o δ hδ N f (by positivity)
  intro a x hx
  have hd := cartesianDualCell_dist_le o δ hδ N hh hstep a hx
  have hf' := hf.dist_le_mul x (cartesianInteriorPoint o δ N a)
  rw [Real.dist_eq] at hf'
  exact hf'.trans (by nlinarith [mul_le_mul_of_nonneg_left hd C.coe_nonneg])

end Carleman
