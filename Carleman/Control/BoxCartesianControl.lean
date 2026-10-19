module

public import Carleman.Control.BoxCartesianObservation
public import Carleman.Control.RelaxedControl

/-! Actual physical Cartesian controls obtained from the proved box observation estimate. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_cartesian_physical_control (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W ω : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) (hω : IsOpen ω) (hinc : closure W ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ qc κ h0 Δ0 Cb d0 : ℝ, 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cb ∧ 0 < d0 ∧
      ∀ (T M : ℝ), 0 < T → 0 ≤ M → ∃ C : ℝ, 0 < C ∧
      ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ),
        openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=openCoordinateBox lo hi →
      ∀ h : ℝ, 0 < h → h ≤ h0 → (∀ j, h/ratio ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ g : TimeGrid, g.period = T → g.dt ≤ Δ0 →
        let Smax := physicalMeshScale κ h g.dt
        16*physicalBaseAmplitude Cb qc T M ≤ Smax →
        Smax ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
      ∀ b : Fin g.steps → CartesianInteriorIndex N → ℝ, (∀ i a, |b i a| ≤ M) →
      ∀ y0 : CartesianPhysicalState δ hδ N,
        ∃ u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω,
        ∃ y : Fin (g.steps+1) → CartesianPhysicalState δ hδ N,
          y 0 = y0 ∧ ForwardEquation g.dt
            (fun i => cartesianPhysicalLaplacian o δ hδ N+PhysicalFiniteSpace.multiplier (b i))
            (cartesianPhysicalControlExtension o δ hδ N ω) u y ∧
          controlNorm g.dt u ≤ Real.sqrt C*‖y0‖ ∧
          ‖y (Fin.last g.steps)‖ ≤ Real.sqrt C*Real.exp (-d0*Smax)*‖y0‖ := by
  obtain ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,hobs⟩ :=
    box_cartesian_physical_observability lo hi hpos hW hne hWS hω hinc ratio hratio
  refine ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨C,hC,hdata⟩ := hobs T M hT hM
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hdom h hh hh0' hlower hupper g hg hdt Smax hS hmesh hsmall hdtT b hb
  have ho := hdata o δ hδ N hdom h hh hh0' hlower hupper g hg hdt hS hmesh hsmall hdtT b hb
  exact relaxed_control_of_observation g M d0 Smax C hsmall hC.le
    (cartesianPhysicalLaplacian o δ hδ N) (cartesianPhysicalLaplacian_symmetric o δ hδ N)
    (cartesianPhysicalLaplacian_nonneg o δ hδ N) (fun i => PhysicalFiniteSpace.multiplier (b i))
    (fun i => PhysicalFiniteSpace.multiplier_symmetric (b i))
    (fun i => PhysicalFiniteSpace.multiplier_opNorm_le (b i) M hM (hb i))
    (cartesianPhysicalControlExtension o δ hδ N ω) ho

end Carleman.Physical
