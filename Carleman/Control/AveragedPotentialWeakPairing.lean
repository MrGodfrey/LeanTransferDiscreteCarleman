module

public import Carleman.Control.PotentialWeakPairing

/-! Potential terms for the original finite-element and finite-difference averages. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman

theorem timeAveragedPotential_weak_pairing
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b φ : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν))
    (u v : ℕ → Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod ν))
    (y : Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod ν)) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ w : Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod ν),
      Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w)))
    (hv : Tendsto v atTop (𝓝 φ.toL2)) :
    Tendsto (fun n => inner ℝ ((fixedTimePotential T (g n) (hT n) b).map (u n)) (v n))
      atTop (𝓝 (inner ℝ (b.map y) φ.toL2)) :=
  potential_weak_pairing_tendsto (fun n => fixedTimePotential T (g n) (hT n) b) b φ
    (fun n => (fixedTimePotential_bound T (g n) (hT n) b).le)
    (timeAveragedPotential_strong_convergence T hTpos g hT htlim b) u v y hu hweak hv

theorem cartesianAveragedPotential_weak_pairing {d : ℕ}
    (T : ℝ) (hTpos : 0 ≤ T) (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b φ : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    (u v : ℕ → Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    (y : Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ w : Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))),
      Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w)))
    (hv : Tendsto v atTop (𝓝 φ.toL2)) :
    Tendsto (fun n => inner ℝ
      ((fixedSpacetimePotential T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).map (u n)) (v n))
      atTop (𝓝 (inner ℝ (b.map y) φ.toL2)) :=
  potential_weak_pairing_tendsto
    (fun n => fixedSpacetimePotential T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b) b φ
    (fun n => (fixedSpacetimePotential_bound T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).le)
    (cartesianAveragedPotential_strong_convergence T hTpos lo hi δ hδ N hN hbox g hT h hh hstep hlim htlim b)
    u v y hu hweak hv

end Carleman
