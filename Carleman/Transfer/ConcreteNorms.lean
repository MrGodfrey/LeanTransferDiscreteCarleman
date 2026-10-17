module

public import Carleman.Spatial.Observation
public import Carleman.Transfer.Comparison

/-! Direct constructors for the temporal part of ComparisonBridge's B3 fields.
The remaining nodewise spatial numerical bounds remain explicit. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.TransferGeometry
variable {H X F Y Ω K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  [MeasurableSpace Ω] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  {ν : Measure Ω} [SFinite ν] {V : Submodule ℝ H} {a : CarlemanExponents}
  (p : TransferGeometry V X F Y a) (ρ : SpatialProfile ν) {g : TimeGrid} {β : ℝ}
  (hq : TimeWeightRegularity p.weight g β) (r : Reconstruction V X)
include hq

/-- Supplies node_derivative and finite_reconstructionD from a genuine L² field realization. -/
theorem node_derivative_of_L2 (j : Fin a.m) (J : V →ₗ[ℝ] Lp K 2 ν)
    (τ τStar : ℝ) (hp : p.derivative j = fun t => (ρ.multiplier p.weight τ t).seminorm.comp J)
    (hτ : |τ+a.c j/2| ≤ τStar) (hm : β*g.dt*p.weight.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*p.weight.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X) :
    TimeSquareIntegrable g p.weight.q (a.c j) (p.derivative j) (p.reconstruction g r s z) ∧
      g.powerSq (p.weight.nodes g) (a.c j) (p.node g (p.derivative j)) (fun i => r.R (z i)) ≤
        9*timeSq g p.weight.q (a.c j) (p.derivative j) (p.reconstruction g r s z) := by
  have hc := ρ.powerSq_timeSq_comparison_comp hq J s τ (a.c j) τStar hτ hm hmw (fun i => r.R (z i))
  rw [hp]
  cases s <;> exact ⟨hc.1, hc.2.2⟩

/-- Supplies node_state from the numerical spatial lower bound and proved cell comparison. -/
theorem node_state_of_L2 (J : H →ₗ[ℝ] Lp K 2 ν) (τ τStar C : ℝ) (hC : 0 ≤ C)
    (hp : p.space = fun t => (ρ.multiplier p.weight τ t).seminorm.comp J)
    (hτ : |τ+a.c₀/2| ≤ τStar) (hm : β*g.dt*p.weight.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*p.weight.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X)
    (hn : ∀ i, (p.state (g.nodeTime i) (z i))^2 ≤ C*(p.space (g.nodeTime i) (r.RH (z i)))^2) :
    g.powerSq (p.weight.nodes g) a.c₀ (p.node g p.state) z ≤
      (9*C)*timeSq g p.weight.q a.c₀ p.space (fun t => r.RH (s.extension g z t)) := by
  rw [hp] at hn ⊢
  have hc := ρ.node_powerSq_le_reconstruction hq (fun x => J (r.RH x)) s τ a.c₀ τStar hτ hm hmw
    (p.node g p.state) z C hC hn
  cases s <;> exact hc

omit r in
/-- Supplies lifted_load, preserving an ordinary lift rather than requiring linearity. -/
theorem lifted_load_of_L2 (J : H →ₗ[ℝ] Lp K 2 ν) (lift : F → H) (τ τStar C : ℝ)
    (hp : p.space = fun t => (ρ.multiplier p.weight τ t).seminorm.comp J)
    (hτ : |τ| ≤ τStar) (hm : β*g.dt*p.weight.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*p.weight.max^2 ≤ 1)
    (s : Orientation) (f : g.Sequence F)
    (hn : ∀ i, (p.space (g.nodeTime i) (lift (f i)))^2 ≤ C*(p.load (g.nodeTime i) (f i))^2) :
    timeSq g p.weight.q 0 p.space (s.extension g (fun i => lift (f i))) ≤ (9*C)*p.loadSq g f := by
  rw [hp] at hn ⊢
  have hc := ρ.lifted_timeSq_le hq (fun x => J (lift x)) s τ 0 τStar (by simpa using hτ)
    hm hmw (p.node g p.load) f C hn
  rw [TimeGrid.powerSq_zero] at hc
  cases s <;> exact hc

/-- Supplies observed_reconstruction from the original nodal observation compatibility. -/
theorem observed_reconstruction_of_L2 (J : H →ₗ[ℝ] Lp K 2 ν) (Bstar : X →ₗ[ℝ] Y)
    (τ τStar C : ℝ) (hp : p.observation = fun t => (ρ.multiplier p.weight τ t).seminorm.comp J)
    (hτ : |τ+a.o/2| ≤ τStar) (hm : β*g.dt*p.weight.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*p.weight.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X)
    (hn : ∀ i, (p.observation (g.nodeTime i) (r.RH (z i)))^2 ≤
      C*(p.control (g.nodeTime i) (Bstar (z i)))^2) :
    timeSq g p.weight.q a.o p.observation (fun t => r.RH (s.extension g z t)) ≤
      (9*C)*p.observationSq g Bstar z := by
  rw [hp] at hn ⊢
  have hc := ρ.lifted_timeSq_le hq (fun x => J (r.RH x)) s τ a.o τStar hτ hm hmw
    (fun i => (p.control (g.nodeTime i)).comp Bstar) z C hn
  cases s <;> exact hc
end Carleman.TransferGeometry
