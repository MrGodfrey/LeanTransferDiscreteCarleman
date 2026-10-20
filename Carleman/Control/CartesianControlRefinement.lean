module

public import Carleman.Control.PhysicalRefinement
public import Carleman.Control.FixedBoxControlData
public import Carleman.Control.BoxCartesianControl
public import Carleman.Spatial.CartesianCellStrongConvergence

/-! Actual HUM controls and states on every sufficiently fine mesh, with original data and endpoints. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
namespace Physical
set_option maxHeartbeats 3000000 in
theorem box_cartesian_controls_independent_refinement (lo hi : Fin (d+1) → ℝ)
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
        Tendsto (fun n => E (n+J) (y n (Fin.last (g (n+J)).steps))) atTop (𝓝 0) := by
  obtain ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,hcontrol⟩ :=
    box_cartesian_physical_control lo hi hpos hW hne hWS hsharp hWsharp ratio hratio
  obtain ⟨hs, hhs, hcells⟩ := cartesianDualCell_subset_region hc hω hinc
  refine ⟨κ,d0,hκ,hd0,?_⟩
  intro T M hTpos hM
  obtain ⟨C,hC,hdata⟩ := hcontrol T M hTpos hM
  refine ⟨C,hC,?_⟩
  intro δ hδ N hN hbox h hh hlower hupper hlim g hT htlim b hb y0 E bg
  have hqb : 0 < physicalBaseAmplitude Cb qc T M := by
    have hx := (physicalBaseAmplitude_bounds Cb qc T M hCb.le (by linarith) hTpos hM).1
    exact (mul_pos hCb (by linarith)).trans_le hx
  have hevent := physical_conditions_eventually (M := M) hκ hh0 hΔ0 hqb hTpos
    h (fun n => (g n).dt) hh (fun n => (g n).dt_pos) hlim htlim
  have hevent' : ∀ᶠ n in atTop, h n ≤ hs ∧ h n ≤ h0 ∧ (g n).dt ≤ Δ0 ∧
      16*physicalBaseAmplitude Cb qc T M ≤ physicalMeshScale κ (h n) (g n).dt ∧
      physicalMeshScale κ (h n) (g n).dt ≤ physicalBaseAmplitude Cb qc T M*T/(4*(g n).dt) ∧
      (g n).dt*M ≤ 1/2 ∧ (g n).dt ≤ T/12 := by
    filter_upwards [hlim.eventually (gt_mem_nhds hhs),hevent] with n hn he
    exact ⟨hn.le,he⟩
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hevent'
  have hgood n := hJ (n+J) (Nat.le_add_left J n)
  have hex n := hdata lo (δ (n+J)) (hδ (n+J)) (N (n+J))
    (by rw [funext (hbox (n+J))]) (h (n+J)) (hh (n+J)) (hgood n).2.1
    (hlower (n+J)) (hupper (n+J)) (g (n+J)) (hT (n+J)) (hgood n).2.2.1
    (hgood n).2.2.2.1 (hgood n).2.2.2.2.1 (hgood n).2.2.2.2.2.1 (hgood n).2.2.2.2.2.2
    (cartesianAveragedPotential lo (δ (n+J)) (N (n+J)) (g (n+J)) (bg (n+J)))
    (fun i a => (cartesianAveragedPotential_bound lo (δ (n+J)) (hδ (n+J)) (N (n+J)) (g (n+J)) (bg (n+J)) i a).trans
      (by simpa only [bg,cartesianGridPotential_bound] using hb))
    ((E (n+J)).toContinuousLinearMap.adjoint y0)
  choose u y hy0 hy hu hyT using hex
  have havg n : ‖(E (n+J)).toContinuousLinearMap.adjoint y0‖ ≤ ‖y0‖ :=
    cartesianBoxCellIsometry_average_norm lo hi (δ (n+J)) (hδ (n+J)) (N (n+J)) (hbox (n+J)) y0
  have hterminal : Tendsto (fun n => ‖y n (Fin.last (g (n+J)).steps)‖) atTop (𝓝 0) := by
    apply physical_terminal_norm_tendsto_zero hκ hd0
      (fun n => h (n+J)) (fun n => (g (n+J)).dt) (fun n => hh (n+J)) (fun n => (g (n+J)).dt_pos)
      (hlim.comp (tendsto_add_atTop_nat J)) (htlim.comp (tendsto_add_atTop_nat J))
      (fun n => y n (Fin.last (g (n+J)).steps))
    intro n
    exact (hyT n).trans (mul_le_mul_of_nonneg_left (havg n) (by positivity))
  refine ⟨J,u,y,(fun n => (hgood n).2.2.2.2.2.1),?_,?_,hterminal,?_⟩
  · intro n
    refine ⟨hy0 n,hy n,hu n,hyT n,?_,?_⟩
    · rw [cartesianBoxTimeControl_norm]
      exact (hu n).trans (mul_le_mul_of_nonneg_left (havg n) (Real.sqrt_nonneg C))
    · exact cartesianBoxTimeControl_supported T lo hi (δ (n+J)) (hδ (n+J)) (N (n+J)) (hbox (n+J))
        (g (n+J)) (hT (n+J)) ωsharp ω hω.measurableSet
        (hcells lo (δ (n+J)) (hδ (n+J)) (N (n+J)) (h (n+J)) (hh (n+J)) (hgood n).1 (hupper (n+J))) (u n)
  · simp only [hy0]
    exact (cartesianBoxCell_average_strong_convergence lo hi δ hδ N hN hbox h (fun n => (hh n).le)
      hupper hlim y0).comp (tendsto_add_atTop_nat J)
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [LinearIsometry.norm_map] using hterminal

end Physical
end Carleman
