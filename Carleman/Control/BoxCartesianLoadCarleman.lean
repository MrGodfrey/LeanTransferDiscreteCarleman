module

public import Carleman.Transfer.BoxCartesianHeatEstimate
public import Carleman.Spatial.CartesianCountWeights
public import Carleman.Control.PhysicalIntervalQClass
public import Carleman.Control.PhysicalLoadCarleman

/-! The actual physical load Carleman estimate for the complete Cartesian box state space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def cartesianInteriorCountProfile (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (c : SpatialCoordinates d) {l : ℝ} (hl : 0 ≤ l) :
    SpatialProfile (Measure.count : Measure (CartesianInteriorIndex N)) :=
  cartesianCountProfile o δ N (interiorCarlemanProfile c l) 2 (by norm_num) (fun x => by
    obtain ⟨hlo,hhi⟩ := interiorCarlemanProfile_bounds c hl x
    exact abs_le.mpr ⟨hlo.le,by linarith⟩)

theorem cartesianInteriorCountProfile_negative (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (c : SpatialCoordinates d) {l : ℝ} (hl : 0 ≤ l) :
    ∀ᵐ a ∂(Measure.count : Measure (CartesianInteriorIndex N)),
      (cartesianInteriorCountProfile o δ N c hl).value a ≤ -1 :=
  Filter.Eventually.of_forall fun a => (interiorCarlemanProfile_bounds c hl
    (cartesianInteriorPoint o δ N a)).2

theorem box_cartesian_physical_load_carleman (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W ω : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) (hω : IsOpen ω) (hinc : closure W ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc κ h0 Δ0 C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < C ∧
      ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ),
        openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=openCoordinateBox lo hi →
      ∀ (h : ℝ), 0 < h → h ≤ h0 → (∀ j, h/ratio ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ (g : TimeGrid) (w : TimeWeight), Physical.PhysicalQClass w g.period β qc → g.dt ≤ Δ0 →
        w.max ≤ κ*min (h^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) →
      Physical.PhysicalLoadCarleman (cartesianInteriorCountProfile o δ N c (zero_le_one.trans hl)) w g
        (cartesianPhysicalLaplacian o δ hδ N) (cartesianCountLpEquiv δ hδ N).toLinearMap
        (cartesianCountObservation o δ hδ N ω) (cartesianCountLpEquiv δ hδ N).symm.toLinearMap C := by
  obtain ⟨c,l,β,qc,κ,h0,Δ0,C,hc,hl,hβ,hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hC,_hphase,hce⟩ :=
    box_cartesian_heat_estimate lo hi hpos hW hne hWS hω hinc ratio hratio
  refine ⟨c,l,β,qc,κ,h0,Δ0,C,hc,hl,hβ,hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hC,?_⟩
  intro o δ hδ N hdom h hh hh0' hlower hupper g w hq hdt hscale
  let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox lo hi)) c (zero_le_one.trans hl)
  let ρh := cartesianInteriorCountProfile o δ N c (zero_le_one.trans hl)
  let E := cartesianCountLpEquiv δ hδ N
  let O := cartesianCountObservation o δ hδ N ω
  let p := cartesianHeatGeometry (openCoordinateBox_isOpen lo hi) o δ hδ N ρ w W ω hW.measurableSet
  let r : Reconstruction (dirichletSubspace (openCoordinateBox lo hi)) (CartesianPhysicalState δ hδ N) :=
    hdom ▸ cartesianReconstruction o δ hδ N
  have hw : p.weight = w := rfl
  have hstate (t : ℝ) (x : CartesianPhysicalState δ hδ N) :
      p.state t x = (ρh.multiplier w 0 t).seminorm (E x) :=
    (cartesianCountProfile_seminorm o δ hδ N _ _ _ _ w 0 t x).symm
  have hcontrol (t : ℝ) (x : CartesianPhysicalState δ hδ N) :
      p.control t ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint x) =
        (ρh.multiplier w 0 t).seminorm (O x) :=
    (cartesianCountProfile_observation o δ hδ N ω _ _ _ _ w 0 t x).symm
  intro z f hz
  have hleft : Physical.physicalWeightedCubeSq ρh w g (fun i => E (z i)) ≤ p.nodeEnergy g r z := by
    have hh := p.zeroth_le_nodeEnergy g r z
    simpa only [CarlemanExponents.heat,TimeGrid.powerSq,TimeWeight.nodes,
      TransferGeometry.node,hw,hstate,Real.rpow_ofNat,Physical.physicalWeightedCubeSq] using hh
  have hload : g.weightedSq (p.node g p.state)
      (Orientation.minus.difference g z+g.map (cartesianPhysicalLaplacian o δ hδ N).toLinearMap z) =
      Physical.physicalWeightedSq ρh w g f := by
    have he : Orientation.minus.difference g z+g.map (cartesianPhysicalLaplacian o δ hδ N).toLinearMap z =
        fun i => E.symm (f i) := by
      funext i
      exact hz i
    rw [he]
    simp only [TimeGrid.weightedSq,TransferGeometry.node,hstate,E.apply_symm_apply,
      Physical.physicalWeightedSq]
  have hobs : p.observationSq g (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap z =
      Physical.physicalWeightedCubeSq ρh w g (fun i => O (z i)) := by
    simp only [TransferGeometry.observationSq,CarlemanExponents.heat,TimeGrid.powerSq,
      TimeWeight.nodes,TransferGeometry.node,hw,ContinuousLinearMap.coe_coe,hcontrol,
      Real.rpow_ofNat,Physical.physicalWeightedCubeSq]
  have hhce := hce o δ hδ N hdom h hh hh0' hlower hupper g w hq.toInterval hdt hscale .minus z
  change p.nodeEnergy g r z ≤ C * (_ + p.observationSq g _ z) at hhce
  rw [hload,hobs] at hhce
  exact hleft.trans hhce

end Carleman
