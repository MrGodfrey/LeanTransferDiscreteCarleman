module

public import Carleman.Control.BoxCartesianObservation
public import Carleman.Control.FilteredObservation

/-! Full Cartesian equations with filtering only of terminal adjoint data. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_cartesian_filtered_observability (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W ω : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) (hω : IsOpen ω) (hinc : closure W ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ qc κ h0 Δ0 Cb d0 : ℝ, 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cb ∧ 0 < d0 ∧
      ∀ (T M : ℝ), 0 < T → 0 ≤ M → ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ),
        openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=openCoordinateBox lo hi →
      ∀ h : ℝ, 0 < h → h ≤ h0 → (∀ j, h/ratio ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ g : TimeGrid, g.period = T → g.dt ≤ Δ0 →
        let Smax := physicalMeshScale κ h g.dt
        16*physicalBaseAmplitude Cb qc T M ≤ Smax →
        Smax ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
      ∀ b : Fin g.steps → CartesianInteriorIndex N → ℝ, (∀ i a, |b i a| ≤ M) →
      ∀ (θ : ℝ) (F : Submodule ℝ (CartesianPhysicalState δ hδ N)),
        T*filterRayleigh (cartesianPhysicalLaplacian o δ hδ N) F ≤ θ*d0*Smax →
        M*T+M^2*T^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d0*Smax →
      ∀ p : Fin (g.steps+1) → CartesianPhysicalState δ hδ N,
        AdjointEquation g.dt (fun i => cartesianPhysicalLaplacian o δ hδ N+
          PhysicalFiniteSpace.multiplier (b i)) p → p (Fin.last g.steps) ∈ F →
        ‖p 0‖^2 ≤ 2*C0*(g.dt*∑ i : Fin g.steps,
          ‖(cartesianPhysicalControlExtension o δ hδ N ω).adjoint (p i.castSucc)‖^2) := by
  obtain ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,hobs⟩ :=
    box_cartesian_physical_observability lo hi hpos hW hne hWS hω hinc ratio hratio
  refine ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨C,_hC,hdata⟩ := hobs T M hT hM
  let C0 := max 1 C
  refine ⟨C0,le_max_left _ _,?_⟩
  intro o δ hδ N hdom h hh hh0' hlower hupper g hg hdt Smax hS hmesh hsmall hdtT b hb θ F hΛ hgap p hp hF
  have ho (z : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
      (hz : AdjointEquation g.dt (fun i => cartesianPhysicalLaplacian o δ hδ N+
        PhysicalFiniteSpace.multiplier (b i)) z) :
      ‖z 0‖^2 ≤ C0*((g.dt*∑ i : Fin g.steps,
        ‖(cartesianPhysicalControlExtension o δ hδ N ω).adjoint (z i.castSucc)‖^2)+
        Real.exp (-2*d0*Smax)*‖z (Fin.last g.steps)‖^2) := by
    apply (hdata o δ hδ N hdom h hh hh0' hlower hupper g hg hdt hS hmesh hsmall hdtT b hb z hz).trans
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    exact add_nonneg (mul_nonneg g.dt_pos.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  apply filtered_observation_of_relaxed g M θ d0 Smax C0 hM hsmall (le_max_left _ _)
    (cartesianPhysicalLaplacian o δ hδ N) (cartesianPhysicalLaplacian_symmetric o δ hδ N)
    (cartesianPhysicalLaplacian_nonneg o δ hδ N) (fun i => PhysicalFiniteSpace.multiplier (b i))
    (fun i => PhysicalFiniteSpace.multiplier_symmetric (b i))
    (fun i => PhysicalFiniteSpace.multiplier_opNorm_le (b i) M hM (hb i))
    (cartesianPhysicalControlExtension o δ hδ N ω) ho F _ _ p hp hF
  · simpa only [hg] using hΛ
  · simpa only [hg] using hgap

end Carleman.Physical
