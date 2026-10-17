module

public import Carleman.Periodic.L2Algebra
public import Carleman.Spatial.AllowedWeight

/-! The actual nodal weight commutator with either cyclic difference.
Smallness is measured against the manuscript's nodal shift, uniformly in T. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem weight_oriented_quotient (s : Orientation) (τ r τStar R : ℝ)
    (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (hmw : (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1)
    (i : g.Index) :
    |(allowedWeight (w := w) τ r (g.nodeTime i) /
      allowedWeight (w := w) τ r (g.nodeTime (s.neighbor g i)) - 1) / g.dt| ≤
        (8*β*(τStar+R))*w.nodes g (s.neighbor g i)^2 := by
  have hp : allowedWeight (w := w) τ r 0 = allowedWeight (w := w) τ r g.period := by
    simp only [allowedWeight,h.endpoint]
  have hb {a b : ℝ} (ha : a ∈ Icc 0 g.period) (hb : b ∈ Icc 0 g.period)
      (hd : |b-a| ≤ g.dt) :
      |(allowedWeight (w := w) τ r b / allowedWeight (w := w) τ r a - 1)/g.dt| ≤
        (8*β*(τStar+R))*w.q a^2 := by
    rw [abs_div,abs_of_pos g.dt_pos]
    apply (div_le_iff₀ g.dt_pos).mpr
    exact (h.relative_weight τ r τStar R hτ hr ha hb hd hm hmw).trans_eq (by ring)
  cases s
  · let j := g.prev i
    have he := hb (g.cellTime_mem j.val (Nat.le_of_lt j.isLt))
      (g.cellTime_mem (j.val+1) (Nat.succ_le_of_lt j.isLt))
      (by rw [g.cellTime_succ_sub,abs_of_pos g.dt_pos])
    rw [g.next_node_value _ hp j] at he
    simpa only [j, TimeGrid.next_prev, Orientation.neighbor, TimeWeight.nodes,
      TimeGrid.cellTime, TimeGrid.nodeTime] using he
  · have he := hb (g.cellTime_mem (i.val+1) (Nat.succ_le_of_lt i.isLt))
      (g.cellTime_mem i.val (Nat.le_of_lt i.isLt))
      (by rw [abs_sub_comm,g.cellTime_succ_sub,abs_of_pos g.dt_pos])
    rw [g.next_node_value _ hp i,g.next_node_value w.q h.endpoint i] at he
    exact he
end TimeWeightRegularity

namespace SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω} (ρ : SpatialProfile ν)

def nodeMap (g : TimeGrid) (w : TimeWeight) (τ : ℝ) :
    g.Sequence (Lp E 2 ν) →ₗ[ℝ] g.Sequence (Lp E 2 ν) where
  toFun u i := (ρ.multiplier w τ (g.nodeTime i)).map (u i)
  map_add' u v := funext fun i => (ρ.multiplier w τ (g.nodeTime i)).map_add (u i) (v i)
  map_smul' c u := funext fun i => (ρ.multiplier w τ (g.nodeTime i)).map_smul c (u i)

def eulerTimeCommutator (g : TimeGrid) (s : Orientation) (w : TimeWeight) (τ : ℝ)
    (u : g.Sequence (Lp E 2 ν)) : g.Sequence (Lp E 2 ν) :=
  s.difference g (ρ.nodeMap g w τ u) - ρ.nodeMap g w τ (s.difference g u)

theorem eulerTimeCommutator_eq (g : TimeGrid) (s : Orientation) (w : TimeWeight) (τ : ℝ)
    (u : g.Sequence (Lp E 2 ν)) (i : g.Index) :
    ρ.eulerTimeCommutator g s w τ u i = g.dt⁻¹ •
      ((ρ.multiplier w τ (g.nodeTime i)).map (u (s.neighbor g i)) -
        (ρ.multiplier w τ (g.nodeTime (s.neighbor g i))).map (u (s.neighbor g i))) := by
  simp only [eulerTimeCommutator,Pi.sub_apply,Orientation.difference_neighbor,nodeMap,
    LinearMap.coe_mk,AddHom.coe_mk,BoundedMultiplier.map_smul]
  change g.dt⁻¹ • (_ - _) - g.dt⁻¹ •
    ((ρ.multiplier w τ (g.nodeTime i)).linearMap (u i - u (s.neighbor g i))) = _
  rw [map_sub]
  simp only [BoundedMultiplier.linearMap, LinearMap.coe_mk, AddHom.coe_mk]
  change g.dt⁻¹ • (_ - _) - g.dt⁻¹ • (_ - _) = _
  module

theorem eulerTimeCommutator_node_le {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (h : TimeWeightRegularity w g β) (s : Orientation) (τ τStar : ℝ)
    (hτStar : 0 ≤ τStar) (hτ : |τ| ≤ τStar)
    (hm : g.dt*w.max^2 ≤ cellThreshold β τStar ρ.bound)
    (u : g.Sequence (Lp E 2 ν)) (i : g.Index) :
    ‖ρ.eulerTimeCommutator g s w τ u i‖ ≤
      (8*β*(τStar+ρ.bound))*w.nodes g (s.neighbor g i)^2 *
        ‖ρ.nodeMap g w τ u (s.neighbor g i)‖ := by
  obtain ⟨hb,hw⟩ := h.mesh_bounds τStar ρ.bound hτStar ρ.bound_nonneg hm
  let j := s.neighbor g i
  let a := ρ.multiplier w τ (g.nodeTime i)
  let b := ρ.multiplier w τ (g.nodeTime j)
  rw [ρ.eulerTimeCommutator_eq]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ρ.bounded,a.map_ae (u j),b.map_ae (u j),
    Lp.coeFn_sub (a.map (u j)) (b.map (u j)),
    Lp.coeFn_smul g.dt⁻¹ (a.map (u j)-b.map (u j))] with x hx ha hb' hs hd
  change ‖(g.dt⁻¹ • (a.map (u j)-b.map (u j))) x‖ ≤ _
  rw [hd]
  change ‖g.dt⁻¹ • ((a.map (u j)-b.map (u j)) x)‖ ≤ _
  rw [hs]
  change ‖g.dt⁻¹ • (a.map (u j) x-b.map (u j) x)‖ ≤ _
  rw [ha,hb']
  change _ ≤ _ * ‖b.map (u j) x‖
  rw [hb']
  have hpos : 0 < b.value x := TimeWeightRegularity.allowedWeight_pos τ (ρ.value x) _
  have he : g.dt⁻¹ • (a.value x • u j x - b.value x • u j x) =
      ((a.value x / b.value x - 1)/g.dt) • (b.value x • u j x) := by
    rw [← sub_smul,smul_smul,smul_smul]
    congr 1
    field_simp
  rw [he,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (h.weight_oriented_quotient s τ (ρ.value x) τStar ρ.bound
    hτ hx hb hw i) (norm_nonneg _)

/-- Every requested positive absorption budget is reached by a structural L
threshold chosen before the grid, weight, direction, exponent or state. -/
theorem eulerTimeCommutator_small_uniform (m : ℕ) (hm : 0 < m)
    (β τStar η : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) (hη : 0 < η) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ u : g.Sequence (Lp E 2 ν),
          g.l2Norm (ρ.eulerTimeCommutator g s w τ u) ≤
            η*g.l2Norm (fun i => (L*w.nodes g i)^(2*m) • ρ.nodeMap g w τ u i) := by
  let K := 8*β*(τStar+ρ.bound)
  refine ⟨max 1 (K/η), cellThreshold β τStar ρ.bound, le_max_left _ _,
    cellThreshold_pos hβ hτStar ρ.bound_nonneg, ?_⟩
  intro g s w h L τ hL hmesh hτ u
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hK : K ≤ η*L^(2*m) := by
    have h₁ := (div_le_iff₀ hη).mp ((le_max_right _ _).trans hL)
    have h₂ : L ≤ L^(2*m) := by simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 2*m by omega)
    nlinarith
  let v : g.Sequence (Lp E 2 ν) := fun i => (L*w.nodes g i)^(2*m) • ρ.nodeMap g w τ u i
  have he := g.l2Norm_le_of_bound (ρ.eulerTimeCommutator g s w τ u)
    (v ∘ s.neighbor g) hη.le (fun i => ?_)
  · rwa [g.l2Norm_comp_equiv] at he
  let j := s.neighbor g i
  have hq : (w.nodes g j)^2 ≤ (w.nodes g j)^(2*m) :=
    pow_le_pow_right₀ (w.lower _) (by omega)
  have hcoef : K*(w.nodes g j)^2 ≤ η*(L*w.nodes g j)^(2*m) := by
    rw [mul_pow]
    have hK0 : 0 ≤ K := by dsimp [K]; positivity [ρ.bound_nonneg]
    calc
      _ ≤ K*(w.nodes g j)^(2*m) := mul_le_mul_of_nonneg_left hq hK0
      _ ≤ _ := by
        simpa only [mul_assoc, TimeWeight.nodes] using mul_le_mul_of_nonneg_right hK
          (pow_nonneg (w.nonneg (g.nodeTime j)) (2*m))
  have hn : 0 ≤ (L*w.nodes g j)^(2*m) := (even_two_mul m).pow_nonneg _
  change ‖ρ.eulerTimeCommutator g s w τ u i‖ ≤ η*‖(L*w.nodes g j)^(2*m) • _‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
  exact (ρ.eulerTimeCommutator_node_le h s τ τStar hτStar hτ hmesh u i).trans
    ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (by ring))
end SpatialProfile
end Carleman
