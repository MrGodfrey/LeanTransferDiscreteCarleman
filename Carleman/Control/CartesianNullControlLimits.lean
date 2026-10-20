module

public import Carleman.Control.DirichletNullControlState
public import Carleman.Control.CartesianControlWeakAccumulation

/-! Every weak accumulation point of the actual independently refined Cartesian controls produces an original continuous null-control state. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
namespace Physical
set_option maxHeartbeats 6000000 in
theorem box_cartesian_controls_null_limits (lo hi : Fin (d+1) → ℝ)
    (hpos : ∀ j, lo j < hi j) {W ωsharp ω : Set (SpatialCoordinates (d+1))}
    (hW : IsOpen W) (hne : W.Nonempty) (hWS : W ⊆ openCoordinateBox lo hi)
    (hsharp : IsOpen ωsharp) (hWsharp : closure W ⊆ ωsharp)
    (hc : IsCompact (closure ωsharp)) (hω : IsOpen ω) (hinc : closure ωsharp ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ κ d0 : ℝ, 0 < κ ∧ 0 < d0 ∧ ∀ T M : ℝ, 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (δ : ℕ → Fin (d+1) → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin (d+1) → ℕ)
        (_hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
        (h : ℕ → ℝ) (_hh : ∀ n, 0 < h n), (∀ n j, h n/ratio ≤ δ n j) →
        (∀ n j, δ n j ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T),
        Tendsto (fun n => (g n).dt) atTop (𝓝 0) →
      ∀ b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))),
        b.bound ≤ M → ∀ y0 : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi)),
      let E := fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      let bg := fun n => cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b
      ∃ J : ℕ,
      ∃ u : ∀ n, Fin (g (n+J)).steps → CartesianPhysicalControl lo (δ (n+J)) (hδ (n+J)) (N (n+J)) ωsharp,
      ∃ y : ∀ n, Fin ((g (n+J)).steps+1) → CartesianPhysicalState (δ (n+J)) (hδ (n+J)) (N (n+J)),
        (∀ n, (g (n+J)).dt*M ≤ 1/2) ∧
        (∀ n, y n 0=(E (n+J)).toContinuousLinearMap.adjoint y0 ∧
          ForwardEquation (g (n+J)).dt
            (fun i => cartesianPhysicalLaplacian lo (δ (n+J)) (hδ (n+J)) (N (n+J))+
              PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo (δ (n+J)) (N (n+J)) (g (n+J)) (bg (n+J)) i))
            (cartesianPhysicalControlExtension lo (δ (n+J)) (hδ (n+J)) (N (n+J)) ωsharp) (u n) (y n) ∧
          controlNorm (g (n+J)).dt (u n) ≤ Real.sqrt C*‖(E (n+J)).toContinuousLinearMap.adjoint y0‖ ∧
          ‖y n (Fin.last (g (n+J)).steps)‖ ≤
            Real.sqrt C*Real.exp (-d0*physicalMeshScale κ (h (n+J)) (g (n+J)).dt)*‖(E (n+J)).toContinuousLinearMap.adjoint y0‖ ∧
          ‖fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => cartesianBoxCellControl lo hi (δ (n+J)) (hδ (n+J)) (N (n+J)) (hbox (n+J)) ωsharp (u n i))‖ ≤ Real.sqrt C*‖y0‖ ∧
          (∀ᵐ t ∂volume.restrict (Ioc 0 T), fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => cartesianBoxCellControl lo hi (δ (n+J)) (hδ (n+J)) (N (n+J)) (hbox (n+J)) ωsharp (u n i)) t ∈
              supportedRegionSpace ω)) ∧
        Tendsto (fun n => E (n+J) (y n 0)) atTop (𝓝 y0) ∧
        Tendsto (fun n => ‖y n (Fin.last (g (n+J)).steps)‖) atTop (𝓝 0) ∧
        Tendsto (fun n => E (n+J) (y n (Fin.last (g (n+J)).steps))) atTop (𝓝 0) ∧
        let K := fun n => fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
          (fun i => cartesianBoxCellControl lo hi (δ (n+J)) (hδ (n+J)) (N (n+J)) (hbox (n+J)) ωsharp (u n i));
        (∀ a : ℕ → ℕ, ∃ v : Lp (Lp ℝ 2 ((volume.restrict (openCoordinateBox lo hi)).restrict ω)) 2 (volume.restrict (Ioc 0 T)),
          ‖v‖ ≤ Real.sqrt C*‖y0‖ ∧ ∃ χ : ℕ → ℕ, StrictMono χ ∧
          ∀ w, Tendsto (fun n => inner ℝ (K (a (χ n))) w) atTop
            (𝓝 (inner ℝ ((restrictRegionCLM (ν := volume.restrict (openCoordinateBox lo hi)) (E := ℝ) ω).adjoint.compLp v) w))) ∧
        (∀ a : ℕ → ℕ, StrictMono a →
          ∀ U : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)),
          (∀ w, Tendsto (fun n => inner ℝ (K (a n)) w) atTop (𝓝 (inner ℝ U w))) →
          ∃ Y : Lp (DirichletEnergyState (openCoordinateBox lo hi)) 2 (volume.restrict (Ioc 0 T)),
            ‖Y‖ ≤ stateTimeEnergyBound T M ‖y0‖ (Real.sqrt C*‖y0‖) ∧
            ∃ v : Lp (Lp ℝ 2 ((volume.restrict (openCoordinateBox lo hi)).restrict ω)) 2 (volume.restrict (Ioc 0 T)),
              (restrictRegionCLM (ν := volume.restrict (openCoordinateBox lo hi)) (E := ℝ) ω).adjoint.compLp v=U ∧
              ‖v‖ ≤ Real.sqrt C*‖y0‖ ∧
              FiniteDirichletControlIdentity T (openCoordinateBox lo hi) b y0 Y U ∧
              DirichletNullControlState T (openCoordinateBox lo hi) (openCoordinateBox_isOpen lo hi) b y0 Y U) := by
  obtain ⟨κ,d0,hκ,hd0,hcontrol⟩ := box_cartesian_controls_weak_accumulation
    lo hi hpos hW hne hWS hsharp hWsharp hc hω hinc ratio hratio
  refine ⟨κ,d0,hκ,hd0,?_⟩
  intro T M hTpos hM
  obtain ⟨C,hC,hdata⟩ := hcontrol T M hTpos hM
  refine ⟨C,hC,?_⟩
  intro δ hδ N hN hbox h hh hlower hupper hlim g hT htlim b hb y0 E bg
  obtain ⟨J,u,y,hsmall,hall,hy0,hyN,hET,hcompact,hacc⟩ :=
    hdata δ hδ N hN hbox h hh hlower hupper hlim g hT htlim b hb y0
  refine ⟨J,u,y,hsmall,hall,hy0,hyN,hET,hcompact,?_⟩
  intro a ha U hU
  obtain ⟨Y,hY,v,hv,hvbound,hid⟩ := hacc a ha U hU
  exact ⟨Y,hY,v,hv,hvbound,hid,hid.null_control_state hTpos (openCoordinateBox_isOpen lo hi)⟩

end Physical
end Carleman
