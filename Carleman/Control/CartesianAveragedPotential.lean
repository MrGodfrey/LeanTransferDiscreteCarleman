module

public import Carleman.Control.TimeCellAverage
public import Carleman.Spatial.CartesianCellReconstruction
public import Carleman.Spatial.PhysicalFiniteWeights

/-! The original space-time cell averages, as genuine physical potential operators. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
variable (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))

def cartesianAveragedPotential (i : Fin g.steps) (a : CartesianInteriorIndex N) : ℝ :=
  (∏ j, δ j)⁻¹ * ∫ x in cartesianDualCell o δ N a, (timeCellPotential g b i).value x ∂(volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))

include hδ in
theorem cartesianAveragedPotential_formula (i : Fin g.steps) (a : CartesianInteriorIndex N) :
    cartesianAveragedPotential o δ N g b i a = (g.dt*(∏ j, δ j))⁻¹ *
      ∫ t in g.physicalTimeCell i, ∫ x in cartesianDualCell o δ N a, b.value (t,x) := by
  rw [cartesianAveragedPotential,timeCellPotential_setIntegral]
  simp only [Measure.restrict_restrict (cartesianDualCell_measurable o δ N a),
    Set.inter_eq_left.mpr (cartesianDualCell_subset o δ hδ N a)]
  rw [mul_inv_rev]
  ring

include hδ in
theorem cartesianAveragedPotential_bound (i : Fin g.steps) (a : CartesianInteriorIndex N) :
    |cartesianAveragedPotential o δ N g b i a| ≤ b.bound := by
  have hh := (timeCellPotential g b i).setAverage_bound (cartesianDualCell o δ N a)
    (Finset.prod_pos (fun j _ => hδ j)) (cartesianDualCell_restrict_volume o δ hδ N a)
  rw [timeCellPotential_bound] at hh
  exact hh

def cartesianAveragedPotentialMultiplier (i : Fin g.steps) :
    BoundedMultiplier (Measure.count : Measure (CartesianInteriorIndex N)) :=
  .ofFinite (cartesianAveragedPotential o δ N g b i) b.bound b.bound_nonneg
    (cartesianAveragedPotential_bound o δ hδ N g b i)

theorem cartesianAveragedPotential_congr
    (c : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (h : b.value =ᵐ[(volume.restrict (Ioc 0 g.period)).prod (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))] c.value)
    (i : Fin g.steps) (a : CartesianInteriorIndex N) :
    cartesianAveragedPotential o δ N g b i a = cartesianAveragedPotential o δ N g c i a := by
  apply congrArg ((∏ j, δ j)⁻¹ * ·)
  exact integral_congr_ae (ae_restrict_of_ae (timeCellPotential_congr g b c h i))

theorem cartesianAveragedPotential_operator_norm (i : Fin g.steps) :
    ‖PhysicalFiniteSpace.multiplier (mass := ∏ j, δ j) (hmass := Finset.prod_pos (fun j _ => hδ j))
      (cartesianAveragedPotential o δ N g b i)‖ ≤ b.bound :=
  PhysicalFiniteSpace.multiplier_opNorm_le _ _ b.bound_nonneg
    (cartesianAveragedPotential_bound o δ hδ N g b i)

theorem cartesianAveragedPotential_operator_symmetric (i : Fin g.steps) :
    (PhysicalFiniteSpace.multiplier (mass := ∏ j, δ j) (hmass := Finset.prod_pos (fun j _ => hδ j))
      (cartesianAveragedPotential o δ N g b i)).IsSymmetric :=
  PhysicalFiniteSpace.multiplier_symmetric _

end Carleman
