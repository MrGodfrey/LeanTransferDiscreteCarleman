module

public import Carleman.Geometry.LocalLipschitzCharts

/-! Uniform tubes along every direction in an inward cone. The initial ball
lies in both the patch and the domain; this supplies the positive margin needed
to differentiate ordinary mollifications along the entire segment. -/
@[expose] public noncomputable section
open Set Metric
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem InwardConePatch.tube_subset (p : InwardConePatch S) {x z : E} {ε t : ℝ}
    (hx : closedBall x ε ⊆ p.region ∩ S) (hz : ‖z-p.direction‖ ≤ 1)
    (ht : 0 ≤ t) (hheight : t ≤ p.height) : closedBall (x+t • z) ε ⊆ S := by
  rcases eq_or_lt_of_le ht with hzero | ht
  · subst t
    simpa only [zero_smul,add_zero] using hx.trans inter_subset_right
  intro y hy
  let b := y-t • z
  have hb : b ∈ closedBall x ε := by
    rw [mem_closedBall,dist_eq_norm] at hy ⊢
    simpa only [show b-x=y-(x+t • z) by dsimp [b]; abel] using hy
  have hyball : y ∈ closedBall (b+t • p.direction) t := by
    rw [mem_closedBall,dist_eq_norm]
    rw [show y-(b+t • p.direction)=t • (z-p.direction) by dsimp [b]; rw [smul_sub]; abel]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz ht.le
  exact p.inward b (hx hb).1 (hx hb).2 t ht hheight hyball
end Carleman
