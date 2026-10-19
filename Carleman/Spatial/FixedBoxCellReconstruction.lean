module

public import Carleman.Spatial.CartesianCellApproximation

/-! The original reconstructions in one fixed physical L² space throughout mesh refinement. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianBoxCellIsometry (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) :
    CartesianPhysicalState δ hδ N →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi)) :=
  finiteCellIsometry (cartesianDualCell lo δ N) (cartesianDualCell_measurable lo δ N)
    (Finset.prod_pos (fun j _ => hδ j)) (cartesianDualCell_disjoint lo δ hδ N)
    (by intro a; rw [← funext hbox]; exact cartesianDualCell_restrict_volume lo δ hδ N a)

theorem cartesianBoxCellIsometry_adjoint_average (lo hi δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) (a : CartesianInteriorIndex N) :
    ((cartesianBoxCellIsometry lo hi δ hδ N hbox).toContinuousLinearMap.adjoint u) a=
      (∏ j, δ j)⁻¹*(∫ x in cartesianDualCell lo δ N a, u x ∂volume) := by
  have he := funext hbox
  subst hi
  exact cartesianCellIsometry_adjoint_average lo δ hδ N u a

theorem cartesianBoxCellIsometry_average_norm (lo hi δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) :
    ‖(cartesianBoxCellIsometry lo hi δ hδ N hbox).toContinuousLinearMap.adjoint u‖ ≤ ‖u‖ := by
  have he := funext hbox
  subst hi
  exact cartesianCellIsometry_average_norm lo δ hδ N u

theorem cartesianBoxCell_average_error (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : SpatialCoordinates d →ᵇ ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hloc : ∀ a : CartesianInteriorIndex N, ∀ x ∈ cartesianDualCell lo δ N a,
      |f x-f (cartesianInteriorPoint lo δ N a)| ≤ ε) :
    let ν := volume.restrict (openCoordinateBox lo hi)
    let u := BoundedContinuousFunction.toLp 2 ν ℝ f
    let E := cartesianBoxCellIsometry lo hi δ hδ N hbox
    ‖u-E (E.toContinuousLinearMap.adjoint u)‖^2 ≤
      ε^2*ν.real univ+‖f‖^2*ν.real (⋃ a : CartesianInteriorIndex N, cartesianDualCell lo δ N a)ᶜ := by
  have he := funext hbox
  subst hi
  exact cartesianCell_average_continuous_error lo δ hδ N f hε hloc

theorem cartesianBox_uncovered_volume_tendsto (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (hlim : ∀ j, Tendsto (fun n => δ n j) atTop (𝓝 0)) :
    Tendsto (fun n => (volume.restrict (openCoordinateBox lo hi)).real
      (⋃ a : CartesianInteriorIndex (N n), cartesianDualCell lo (δ n) (N n) a)ᶜ) atTop (𝓝 0) := by
  have he n : (volume.restrict (openCoordinateBox lo hi)).real
      (⋃ a : CartesianInteriorIndex (N n), cartesianDualCell lo (δ n) (N n) a)ᶜ=
        (∏ j, (hi j-lo j))-(∏ j, (hi j-lo j-δ n j)) := by
    have hh := cartesianDualCells_uncovered_volume lo (δ n) (hδ n) (N n) (hN n)
    rw [funext (hbox n)] at hh
    have hw j : (N n j:ℝ)*δ n j=hi j-lo j := by linarith [hbox n j]
    simpa only [hw] using hh
  simp_rw [he]
  have hp : Tendsto (fun n => ∏ j, (hi j-lo j-δ n j)) atTop (𝓝 (∏ j, (hi j-lo j))) := by
    apply tendsto_finsetProd
    intro j _
    simpa using tendsto_const_nhds.sub (hlim j)
  simpa using (tendsto_const_nhds (x := ∏ j, (hi j-lo j))).sub hp

end Carleman
