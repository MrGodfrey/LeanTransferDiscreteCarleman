module

public import Carleman.Control.PhysicalLoadCarleman
public import Carleman.Transfer.ScaleExponents
public import Carleman.Transfer.Geometry

/-! The physical q³ load estimate is a consequence of the full heat transfer
estimate on the same periodic states, loads and observation operator. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical
variable {Ω E X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {ν : Measure Ω}
  {V : Submodule ℝ (Lp E 2 ν)}
  (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
  (p : TransferGeometry V X (Lp E 2 ν) Y CarlemanExponents.heat)
  (hw : p.weight = w)

include hw in
theorem physical_cube_le_nodeEnergy (r : Reconstruction V X) (R : X →ₗ[ℝ] Lp E 2 ν)
    (hstate : ∀ t x, p.state t x = (ρ.multiplier w 0 t).seminorm (R x))
    (z : Fin g.steps → X) :
    physicalWeightedCubeSq ρ w g (fun i => R (z i)) ≤ p.nodeEnergy g r z := by
  have hh := p.zeroth_le_nodeEnergy g r z
  simpa only [CarlemanExponents.heat,TimeGrid.powerSq,TimeWeight.nodes,
    TransferGeometry.node,hw,hstate,Real.rpow_ofNat,physicalWeightedCubeSq] using hh

omit hw in
theorem physical_load_eq_transfer
    (hload : ∀ t f, p.load t f = (ρ.multiplier w 0 t).seminorm f)
    (f : Fin g.steps → Lp E 2 ν) :
    p.loadSq g f = physicalWeightedSq ρ w g f := by
  simp only [TransferGeometry.loadSq,TimeGrid.weightedSq,TransferGeometry.node,
    hload,physicalWeightedSq]

include hw in
theorem physical_observation_eq_transfer (Bstar : X →ₗ[ℝ] Y) (O : X →ₗ[ℝ] Lp E 2 ν)
    (hcontrol : ∀ t x, p.control t (Bstar x) = (ρ.multiplier w 0 t).seminorm (O x))
    (z : Fin g.steps → X) :
    p.observationSq g Bstar z = physicalWeightedCubeSq ρ w g (fun i => O (z i)) := by
  simp only [TransferGeometry.observationSq,CarlemanExponents.heat,TimeGrid.powerSq,
    TimeWeight.nodes,TransferGeometry.node,hw,hcontrol,Real.rpow_ofNat,physicalWeightedCubeSq]

include hw in
/-- No physical observation estimate is an input: only the full periodic load
conclusion already supplied by the heat transfer theorem is used here. -/
theorem physical_load_carleman_of_transfer (r : Reconstruction V X)
    (A : X →L[ℝ] X) (R O : X →ₗ[ℝ] Lp E 2 ν) (Bstar : X →ₗ[ℝ] Y)
    (Γ : Lp E 2 ν →ₗ[ℝ] X) (CCE : ℝ)
    (hstate : ∀ t x, p.state t x = (ρ.multiplier w 0 t).seminorm (R x))
    (hload : ∀ t f, p.load t f = (ρ.multiplier w 0 t).seminorm f)
    (hcontrol : ∀ t x, p.control t (Bstar x) = (ρ.multiplier w 0 t).seminorm (O x))
    (hce : ∀ (s : Orientation) (f : g.Sequence (Lp E 2 ν)) (z : g.Sequence X),
      s.difference g z+g.map A.toLinearMap z = (fun i => Γ (f i)) →
      p.nodeEnergy g r z ≤ CCE*(p.loadSq g f+p.observationSq g Bstar z)) :
    PhysicalLoadCarleman ρ w g A R O Γ CCE := by
  intro z f hz
  have he : Orientation.minus.difference g z+g.map A.toLinearMap z = (fun i => Γ (f i)) := by
    funext i
    exact hz i
  have hh := hce .minus f z he
  rw [physical_load_eq_transfer ρ w g p hload,
    physical_observation_eq_transfer ρ w g p hw Bstar O hcontrol] at hh
  exact (physical_cube_le_nodeEnergy ρ w g p hw r R hstate z).trans hh

end Carleman.Physical
