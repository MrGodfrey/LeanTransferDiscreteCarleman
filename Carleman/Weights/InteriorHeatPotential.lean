module

public import Carleman.Weights.InteriorHeatBLowerBound
public import Carleman.Weights.InteriorHeatMatrix

/-! Positivity of the actual heat-cross potential away from an interior observation ball. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ}

def interiorHeatPotential (c : SpatialCoordinates d) (l : ℝ) (x : SpatialCoordinates d) : ℝ :=
  l^3*(interiorGaussian c l x)^3*‖gradient (interiorQuadratic c) x‖^2*
    (l*‖gradient (interiorQuadratic c) x‖^2-6)

theorem interiorHeatPotential_continuous (c : SpatialCoordinates d) (l : ℝ) :
    Continuous (interiorHeatPotential c l) := by
  change Continuous (fun x => interiorHeatPotential c l x)
  simp only [interiorHeatPotential,interiorQuadratic_gradient_norm_sq]
  have hφ := (interiorGaussian_contDiff c l).continuous
  fun_prop

theorem interiorHeatPotential_positive_outside (c : SpatialCoordinates d) {l r κ : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hκ : 0 < κ) {x : SpatialCoordinates d}
    (hx : x ∉ Metric.ball c r) (hφ : κ ≤ interiorGaussian c l x)
    (hgrad : 12 ≤ l*‖gradient (interiorQuadratic c) x‖^2) :
    24*l^3*κ^3*r^2 ≤ interiorHeatPotential c l x := by
  have hg := interiorQuadratic_gradient_outside_ball c hr.le hx
  have hφ3 := pow_le_pow_left₀ hκ.le hφ 3
  have h1 := mul_le_mul_of_nonneg_left hφ3 (show 0 ≤ l^3 by positivity)
  have h2 := mul_le_mul h1 hg (by positivity) (by positivity [interiorGaussian_pos c l x])
  have h3 := mul_le_mul h2 (show 6 ≤ l*‖gradient (interiorQuadratic c) x‖^2-6 by linarith)
    (by norm_num) (by positivity [interiorGaussian_pos c l x])
  dsimp only [interiorHeatPotential]
  nlinarith [h3]

theorem exists_interior_heat_observation_coefficients {S W : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) (hW : IsOpen W) (hne : W.Nonempty) (hWS : W ⊆ S) :
    ∃ (c : SpatialCoordinates d) (l a m K : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < a ∧ 0 < m ∧ 0 < K ∧ ∀ x ∈ S,
      a ≤ l*interiorGaussian c l x ∧
      m ≤ interiorHeatPotential c l x+W.indicator (fun _ => K) x := by
  classical
  obtain ⟨c,r,l,κ,J,hc,hr,hl,hκ,_hJ,hball,_hsmooth,_hnegative,hφ,hgrad,_hmat,_hflux⟩ :=
    exists_interior_heat_weight hS hW hne hWS 6
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  let m := 24*l^3*κ^3*r^2
  have hm : 0 < m := by dsimp only [m]; positivity
  obtain ⟨D,hD⟩ := hS.isCompact_closure.exists_bound_of_continuousOn
    (interiorHeatPotential_continuous c l).continuousOn
  let K := |D|+m
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨c,l,l*κ,m,K,hc,hl,by positivity,hm,hK,?_⟩
  intro x hx
  refine ⟨mul_le_mul_of_nonneg_left (hφ x hx) hl0.le,?_⟩
  by_cases hxW : x ∈ W
  · rw [indicator_of_mem hxW]
    have hh := hD x (subset_closure hx)
    rw [Real.norm_eq_abs] at hh
    have hlo := (abs_le.mp hh).1
    dsimp only [K]
    linarith [le_abs_self D]
  · rw [indicator_of_notMem hxW,add_zero]
    have hxball : x ∉ Metric.ball c r := fun h => hxW (hball (Metric.ball_subset_closedBall h))
    exact interiorHeatPotential_positive_outside c hl0 hr hκ hxball (hφ x hx) (by
      have hh := hgrad x hxball
      norm_num at hh
      exact hh)

end Carleman
