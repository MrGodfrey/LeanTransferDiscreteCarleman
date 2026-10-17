module

public import Carleman.Continuous.EulerTimeEmbedding

/-! Algebra of the actual dt-weighted sequence L² norm. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem l2Norm_add_le (u v : g.Sequence H) :
    g.l2Norm (u + v) ≤ g.l2Norm u + g.l2Norm v := by
  have he : Orientation.plus.extensionLp g (u+v) =
      Orientation.plus.extensionLp g u + Orientation.plus.extensionLp g v := by
    apply Lp.ext
    filter_upwards [Orientation.plus.extensionLp_ae g (u+v),
      Orientation.plus.extensionLp_ae g u, Orientation.plus.extensionLp_ae g v,
      Lp.coeFn_add (Orientation.plus.extensionLp g u) (Orientation.plus.extensionLp g v)]
      with t h1 h2 h3 h4
    rw [h1,h4]
    change _ = Orientation.plus.extensionLp g u t + Orientation.plus.extensionLp g v t
    rw [h2,h3]
    rfl
  simpa only [← Orientation.plus.extensionLp_norm, he] using
    norm_add_le (Orientation.plus.extensionLp g u) (Orientation.plus.extensionLp g v)

theorem l2Norm_neg (u : g.Sequence H) : g.l2Norm (-u) = g.l2Norm u := by
  simp only [l2Norm, weightedNorm, weightedSq, Pi.neg_apply, map_neg_eq_map]

theorem l2Norm_sub_le (u v : g.Sequence H) :
    g.l2Norm (u-v) ≤ g.l2Norm u + g.l2Norm v := by
  simpa only [sub_eq_add_neg, g.l2Norm_neg] using g.l2Norm_add_le u (-v)

theorem l2Norm_comp_equiv (e : g.Index ≃ g.Index) (u : g.Sequence H) :
    g.l2Norm (u ∘ e) = g.l2Norm u := by
  unfold l2Norm weightedNorm weightedSq
  congr 2
  exact e.sum_comp (fun i => (normSeminorm ℝ H (u i))^2)
end Carleman.TimeGrid
