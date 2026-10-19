module

public import Carleman.Spatial.WeakScalarChainRule
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A genuine smooth scalar cutoff separates zero from values with a fixed
positive absolute gap. Its derivative vanishes on both parts of that range. -/
@[expose] public noncomputable section
open Filter Metric
open scoped Topology ContDiff NNReal
namespace Carleman

theorem exists_smooth_gap_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ (η : ℝ → ℝ) (M : ℝ≥0), ContDiff ℝ ∞ η ∧ LipschitzWith M η ∧
      η 0=0 ∧ deriv η 0=0 ∧ ∀ t, δ ≤ |t| → η t=1 ∧ deriv η t=0 := by
  let b : ContDiffBump (0:ℝ) := ⟨δ/4,δ/2,by positivity,by linarith⟩
  obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    (b.contDiff : ContDiff ℝ ∞ b) (by simp)
  let η := fun t => 1-b t
  have hη : ContDiff ℝ ∞ η := contDiff_const.sub b.contDiff
  have hL : LipschitzWith M η := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [η,dist_eq_norm,show (1-b x)-(1-b y)=-(b x-b y) by ring,norm_neg] using hM.dist_le_mul x y
  have hnear : η =ᶠ[𝓝 (0:ℝ)] (fun _ => 0) :=
    b.eventuallyEq_one.mono fun t ht => by dsimp only [η]; rw [ht]; simp
  refine ⟨η,M,hη,hL,hnear.eq_of_nhds,?_,?_⟩
  · rw [hnear.deriv_eq,deriv_const]
  · intro t ht
    have hnot : t ∉ tsupport (b : ℝ → ℝ) := by
      rw [b.tsupport_eq,mem_closedBall,dist_zero_right,Real.norm_eq_abs]
      change ¬ |t| ≤ δ/2
      linarith
    have hb0 : b =ᶠ[𝓝 t] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hnot
    have he : η =ᶠ[𝓝 t] (fun _ => 1) := hb0.mono fun y hy => by dsimp only [η]; rw [hy]; simp
    exact ⟨he.eq_of_nhds,by rw [he.deriv_eq,deriv_const]⟩

end Carleman
