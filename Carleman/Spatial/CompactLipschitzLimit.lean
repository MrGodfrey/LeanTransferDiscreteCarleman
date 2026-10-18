module

public import Carleman.Spatial.LpDominatedLimit
public import Carleman.Spatial.CompactLipschitzSobolev

/-! Strong H¹ convergence of genuine compact Lipschitz jets, from actual
function and derivative convergence and common finite support bounds. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace Carleman
variable {d : ℕ}

theorem firstOrderFields_tendsto
    {u : ℕ → Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {A : ℕ → Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 volume}
    {B : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 volume}
    (hu : Tendsto u atTop (𝓝 v)) (hA : Tendsto A atTop (𝓝 B)) :
    Tendsto (fun n => firstOrderFields (u n) (A n)) atTop (𝓝 (firstOrderFields v B)) := by
  apply tendsto_pi_nhds.mpr
  intro k
  fin_cases k
  · exact ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap.continuous.tendsto v).comp hu
  · exact ((OperatorMultiplier.const derivativeOneFiber).continuousLinearMap.continuous.tendsto B).comp hA

theorem compactLipschitzSobolevJet_tendsto
    {f : ℕ → SpatialCoordinates d → ℝ} {g : SpatialCoordinates d → ℝ}
    {C : ℕ → ℝ≥0} {D : ℝ≥0}
    (hf : ∀ n, LipschitzWith (C n) (f n)) (hg : LipschitzWith D g)
    (hfc : ∀ n, HasCompactSupport (f n)) (hgc : HasCompactSupport g)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hfs : ∀ n, tsupport (f n) ⊆ K) (hgs : tsupport g ⊆ K)
    (B : ℝ) (hB : 0 ≤ B) (hfb : ∀ n x, ‖f n x‖ ≤ B) (hgb : ∀ x, ‖g x‖ ≤ B)
    (L : ℝ) (hL : 0 ≤ L) (hC : ∀ n, (C n : ℝ) ≤ L) (hD : (D : ℝ) ≤ L)
    (hval : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hder : ∀ᵐ x ∂volume, Tendsto (fun n => fderiv ℝ (f n) x) atTop (𝓝 (fderiv ℝ g x))) :
    Tendsto (fun n => compactLipschitzSobolevJet (hf n) (hfc n)) atTop
      (𝓝 (compactLipschitzSobolevJet hg hgc)) := by
  have hu : Tendsto (fun n => compactLipschitzLp (hf n) (hfc n)) atTop
      (𝓝 (compactLipschitzLp hg hgc)) := by
    apply lp_two_tendsto_of_bounded_support _ _ K hK.measurableSet hK.measure_lt_top B hB
    · intro n
      filter_upwards [compactLipschitzLp_ae (hf n) (hfc n)] with x hx
      rw [hx]
      exact ⟨hfb n x,fun hn => image_eq_zero_of_notMem_tsupport (fun hh => hn (hfs n hh))⟩
    · filter_upwards [compactLipschitzLp_ae hg hgc] with x hx
      rw [hx]
      exact ⟨hgb x,fun hn => image_eq_zero_of_notMem_tsupport (fun hh => hn (hgs hh))⟩
    · filter_upwards [ae_all_iff.mpr (fun n => compactLipschitzLp_ae (hf n) (hfc n)),
        compactLipschitzLp_ae hg hgc] with x hx hy
      simpa only [hx,hy] using hval x
  have hA : Tendsto (fun n => compactLipschitzDerivativeLp (hf n) (hfc n)) atTop
      (𝓝 (compactLipschitzDerivativeLp hg hgc)) := by
    apply lp_two_tendsto_of_bounded_support _ _ K hK.measurableSet hK.measure_lt_top L hL
    · intro n
      filter_upwards [compactLipschitzDerivativeLp_ae (hf n) (hfc n)] with x hx
      rw [hx]
      exact ⟨(norm_fderiv_le_of_lipschitz ℝ (hf n)).trans (hC n),
        fun hn => fderiv_of_notMem_tsupport ℝ (fun hh => hn (hfs n hh))⟩
    · filter_upwards [compactLipschitzDerivativeLp_ae hg hgc] with x hx
      rw [hx]
      exact ⟨(norm_fderiv_le_of_lipschitz ℝ hg).trans hD,
        fun hn => fderiv_of_notMem_tsupport ℝ (fun hh => hn (hgs hh))⟩
    · filter_upwards [ae_all_iff.mpr (fun n => compactLipschitzDerivativeLp_ae (hf n) (hfc n)),
        compactLipschitzDerivativeLp_ae hg hgc,hder] with x hx hy hd
      simpa only [hx,hy] using hd
  exact tendsto_subtype_rng.mpr (firstOrderFields_tendsto hu hA)

end Carleman
