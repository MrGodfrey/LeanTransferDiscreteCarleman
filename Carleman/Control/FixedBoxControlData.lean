module

public import Carleman.Control.CartesianWeakLimitTests
public import Carleman.Control.SupportedTimeControl

/-! Original fixed-box potential bound, time-control norm and support. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem cartesianGridPotential_bound (T : ℝ) (lo hi δ : Fin d → ℝ) (N : Fin d → ℕ)
    (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    (cartesianGridPotential T lo hi δ N hbox g hT b).bound=b.bound := by
  have he := funext hbox
  subst hi
  subst T
  rfl

theorem cartesianBoxTimeControl_norm (T : ℝ) (lo hi δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (g : TimeGrid) (hT : g.period=T) (ω : Set (SpatialCoordinates d))
    (u : Fin g.steps → CartesianPhysicalControl lo δ hδ N ω) :
    ‖fixedTimeCellReconstruction T g hT (fun i => cartesianBoxCellControl lo hi δ hδ N hbox ω (u i))‖=
      Physical.controlNorm g.dt u := by
  subst T
  rw [fixedTimeCellReconstruction,timeCellReconstruction_norm]
  simp only [cartesianBoxCellControl,ContinuousLinearMap.coe_comp,Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map,
    cartesianPhysicalControlExtension_norm,Physical.controlNorm]

theorem cartesianBoxTimeControl_supported (T : ℝ) (lo hi δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (g : TimeGrid) (hT : g.period=T) (ωsharp ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (hcell : ∀ a : CartesianInteriorIndex N, cartesianInteriorPoint lo δ N a ∈ ωsharp →
      cartesianDualCell lo δ N a ⊆ ω)
    (u : Fin g.steps → CartesianPhysicalControl lo δ hδ N ωsharp) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      fixedTimeCellReconstruction T g hT (fun i => cartesianBoxCellControl lo hi δ hδ N hbox ωsharp (u i)) t ∈
        Physical.supportedRegionSpace ω := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesianTimeControl_supported lo δ hδ N ωsharp ω hω hcell g u


end Carleman
