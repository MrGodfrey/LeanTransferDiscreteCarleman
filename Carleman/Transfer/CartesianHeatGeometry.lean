module

public import Carleman.Spatial.HeatGradientExpression
public import Carleman.Spatial.CartesianNumericalData

/-! The full Cartesian physical state, load and observation norms in the heat transfer geometry. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
attribute [local instance] Classical.propDecidable

def cartesianLoadInterfaceOn (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) :
    LoadInterface (hdom ▸ cartesianReconstruction o δ hδ N) (CartesianPhysicalState δ hδ N) := by
  subst S
  exact cartesianLoadInterface o δ hδ N

theorem cartesianLoadInterfaceOn_Γ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S)
    (f : CartesianPhysicalState δ hδ N) : (cartesianLoadInterfaceOn o δ hδ N hdom).Γ f = f := by
  subst S
  rfl

theorem cartesianHeatState_definite (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (t : ℝ) (z : CartesianPhysicalState δ hδ N)
    (hz : cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value z = 0) : z = 0 := by
  apply (cartesianStateSeminorm_definite o δ hδ N _ ?_ z).mp hz
  intro i
  simp only [SpatialProfile.multiplier,Real.rpow_zero,one_mul]
  exact (Real.exp_pos _).ne'

theorem cartesianHeatControl_definite (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d))
    (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (t : ℝ) (z : CartesianPhysicalControl o δ hδ N ω)
    (hz : cartesianControlSeminorm o δ hδ N ω (ρ.multiplier w 0 t).value z = 0) : z = 0 := by
  apply (cartesianControlSeminorm_definite o δ hδ N ω _ ?_ z).mp hz
  intro i
  simp only [SpatialProfile.multiplier,Real.rpow_zero,one_mul]
  exact (Real.exp_pos _).ne'

def cartesianHeatGeometry (hS : IsOpen S) (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (W ω : Set (SpatialCoordinates d)) (hW : MeasurableSet W) :
    TransferGeometry (dirichletSubspace S) (CartesianPhysicalState δ hδ N)
      (CartesianPhysicalState δ hδ N) (CartesianPhysicalControl o δ hδ N ω)
      CarlemanExponents.heat :=
  sobolevGeometry hS (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
    w ρ heatDifferentialFamily W hW
    (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
    (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
    (fun t => cartesianControlSeminorm o δ hδ N ω (ρ.multiplier w 0 t).value)
    (cartesianHeatState_definite o δ hδ N ρ w)
    (cartesianHeatState_definite o δ hδ N ρ w)
    (cartesianHeatControl_definite o δ hδ N ω ρ w)

end Carleman
