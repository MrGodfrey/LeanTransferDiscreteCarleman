module
public import Carleman.Spatial.ClassicalConvexHessian
/-! A true divergence sign theorem on compact regular sublevels,
proved by compact cutoffs and a shrinking boundary layer. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem weighted_level_divergence_identity (η g κ : SpatialCoordinates d → ℝ)
    (F : Fin d → SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hchain : ∀ x, fderiv ℝ η x=(-κ x) • fderiv ℝ g x) :
    (∫ x, η x*(∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x))=
      ∫ x, κ x*(∑ i, F i x*graphSlopeVector g x i) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hL (i : Fin d) : Integrable (fun x => η x*smoothD (e i) (F i) x) volume :=
    compact_smooth_product_integrable η _ hη hc (smoothD_contDiff (hF i) _)
  have hR (i : Fin d) : Integrable (fun x => smoothD (e i) η x*F i x) volume :=
    compact_smooth_product_integrable _ _ (smoothD_contDiff hη _) (hc.fderiv_apply ℝ _) (hF i)
  calc
    _ = ∫ x, ∑ i, η x*smoothD (e i) (F i) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Finset.mul_sum _ _ _
    _ = ∑ i, ∫ x, η x*smoothD (e i) (F i) x := integral_finsetSum _ (fun i _ => hL i)
    _ = ∑ i, -(∫ x, smoothD (e i) η x*F i x) :=
      Finset.sum_congr rfl fun i _ => integral_smoothD_compact η (F i) hη hc (hF i) _
    _ = -(∫ x, ∑ i, smoothD (e i) η x*F i x) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact (integral_finsetSum _ (fun i _ => hR i)).symm
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      simp only [← Finset.sum_neg_distrib,Finset.mul_sum,smoothD,hchain,smul_apply,
        smul_eq_mul,graphSlopeVector_apply,e]
      exact Finset.sum_congr rfl fun i _ => by ring

theorem levelLayer_scalar_upper_bound (g F : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hF : Continuous F) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, F c≤0) {δ : ℝ} (hδ : 0<δ) :
    ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε≤r → ∀ x,
      levelLayerWeight g a ε x*F x ≤ δ*(levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2) := by
  let H := fun x => δ*‖graphSlopeVector g x‖^2-F x
  have hH : Continuous H := (continuous_const.mul
    (((graphSlopeVector_contDiff g hg).continuous.norm).pow 2)).sub hF
  have hb : ∀ c ∈ frontier {x | g x<a}, 0<H c := by
    intro c hc
    have hp : 0<‖graphSlopeVector g c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (graphSlopeVector_ne_zero (hreg c hc)))
    exact sub_pos.mpr (lt_of_le_of_lt (hflux c hc) (mul_pos hδ hp))
  obtain ⟨r,hr,hnear⟩ := exists_positive_level_layer g H hg.continuous hH a hK hb
  refine ⟨r,hr,?_⟩
  intro ε hε hεr x
  by_cases hw : levelLayerWeight g a ε x=0
  · simp [hw]
  · have hts : x∈tsupport (levelLayerWeight g a ε) := subset_closure hw
    obtain ⟨hl,hh⟩ := levelLayerWeight_tsupport g hg.continuous a hε hts
    have hxS : x∈{y | g y<a} := by change g x<a;linarith
    have hpos := hnear x (subset_closure hxS) (by linarith)
    have hh' : F x≤δ*‖graphSlopeVector g x‖^2 := by change 0<_-_ at hpos;linarith
    have hmul := mul_le_mul_of_nonneg_left hh' (levelLayerWeight_nonneg g a hε x)
    nlinarith

theorem levelCutoff_divergence_upper_bound (g : SpatialCoordinates d → ℝ)
    (F : Fin d → SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, (∑ i, F i c*graphSlopeVector g c i)≤0)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε≤r →
      (∫ x, levelCutoff g a ε x*(∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x)) ≤
        δ*(∫ x in {x | g x<a}, |spatialLaplacian g x|) := by
  have hfluxsmooth : ContDiff ℝ ∞ (fun x => ∑ i, F i x*graphSlopeVector g x i) :=
    ContDiff.sum fun i _ => (hF i).mul (by
      simp only [graphSlopeVector_apply]
      exact (hg.fderiv_right (by simp)).clm_apply contDiff_const)
  obtain ⟨r,hr,hbound⟩ := levelLayer_scalar_upper_bound g _ hg hfluxsmooth.continuous a hK hreg hflux hδ
  refine ⟨r,hr,?_⟩
  intro ε hε hεr
  have hm : Integrable (fun x => levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2) volume :=
    ((levelLayerWeight_contDiff g hg a ε).continuous.mul
      (((graphSlopeVector_contDiff g hg).continuous.norm).pow 2)).integrable_of_hasCompactSupport
      (levelLayerWeight_compact g hg.continuous a hK hε).mul_right
  have hf := compact_smooth_product_integrable _ _ (levelLayerWeight_contDiff g hg a ε)
    (levelLayerWeight_compact g hg.continuous a hK hε) hfluxsmooth
  have hi := integral_mono hf (hm.const_mul δ) (hbound ε hε hεr)
  rw [integral_const_mul] at hi
  rw [weighted_level_divergence_identity _ g _ F (levelCutoff_contDiff g hg a ε)
    (levelCutoff_compact g hg.continuous a hK hε) hF (levelCutoff_fderiv g hg a ε)]
  exact hi.trans (mul_le_mul_of_nonneg_left (levelCutoff_mass_bound g hg a hK hε) hδ.le)

theorem level_divergence_nonpos (g : SpatialCoordinates d → ℝ)
    (F : Fin d → SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, (∑ i, F i c*graphSlopeVector g c i)≤0) :
    (∫ x in {x | g x<a}, ∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x)≤0 := by
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp [ε];positivity
  have ht : Tendsto ε atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  let L := ∫ x in {x | g x<a}, ∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x
  let M := ∫ x in {x | g x<a}, |spatialLaplacian g x|
  have hdiv : ContDiff ℝ ∞ (fun x => ∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x) :=
    ContDiff.sum fun i _ => smoothD_contDiff (hF i) _
  have hlim := levelCutoff_integral_tendsto g _ hg hdiv.continuous a hK ε hε ht
  have hb (δ : ℝ) (hδ : 0<δ) : L≤δ*M := by
    obtain ⟨r,hr,hbound⟩ := levelCutoff_divergence_upper_bound g F hg hF a hK hreg hflux hδ
    apply le_of_tendsto hlim
    have he : ∀ᶠ n in atTop, ε n<r := ht.eventually (gt_mem_nhds hr)
    filter_upwards [he] with n hn
    exact hbound (ε n) (hε n) hn.le
  have ht' : Tendsto (fun n => ε n*M) atTop (𝓝 (0:ℝ)) := by simpa using ht.mul_const M
  exact ge_of_tendsto ht' (Eventually.of_forall fun n => hb (ε n) (hε n))

end Carleman
