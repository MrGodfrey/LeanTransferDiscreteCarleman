module
public import Carleman.Spatial.FullSpaceDifferenceQuotient
public import Carleman.Spatial.WeakDerivativeStrongLimit
public import Carleman.Spatial.WeakH2BoundedTest
public import Carleman.Spatial.FullSpaceTestPairing
public import Mathlib.Analysis.Calculus.Deriv.Slope
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem spatialDifferenceQuotient_ae (z : SpatialCoordinates d) (h : ℝ)
    {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))} {f : SpatialCoordinates d → ℝ}
    (hu : u =ᵐ[volume] f) :
    spatialDifferenceQuotient z h u =ᵐ[volume] (fun x => h⁻¹*(f (x+h • z)-f x)) := by
  have hs := (measurePreserving_add_right volume (h • z)).quasiMeasurePreserving.ae_eq_comp hu
  rw [spatialDifferenceQuotient_apply]
  filter_upwards [Lp.coeFn_smul h⁻¹ (spatialTranslationLp (h • z) u-u),
    Lp.coeFn_sub (spatialTranslationLp (h • z) u) u,spatialTranslationLp_ae (h • z) u,hs,hu] with x h1 h2 h3 h4 h5
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Function.comp_apply] at *
  rw [h1,h2,h3,h4,h5]

theorem spatialDifferenceQuotient_tendsto_of_contDiff
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f) (z : SpatialCoordinates d)
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hu : u =ᵐ[volume] f) (hv : v =ᵐ[volume] (fun x => fderiv ℝ f x z))
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => spatialDifferenceQuotient z (h n) u) atTop (𝓝 v) := by
  have hne : Tendsto h atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨ht,Eventually.of_forall hh⟩
  have hp (x : SpatialCoordinates d) :
      Tendsto (fun n => (h n)⁻¹*(f (x+h n • z)-f x)) atTop (𝓝 (fderiv ℝ f x z)) := by
    have hg : HasDerivAt (fun t : ℝ => x+t • z) z 0 := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
    have hc : HasDerivAt (fun t : ℝ => f (x+t • z)) (fderiv ℝ f x z) 0 := by
      have hd := (hf.differentiable (by simp) x).hasFDerivAt
      exact hd.comp_hasDerivAt_of_eq 0 hg (by simp)
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul,Function.comp_def] using
      hc.tendsto_slope_zero.comp hne
  have hae : ∀ᵐ x ∂volume,
      Tendsto (fun n => spatialDifferenceQuotient z (h n) u x) atTop (𝓝 (v x)) := by
    filter_upwards [ae_all_iff.mpr (fun n => spatialDifferenceQuotient_ae z (h n) hu),hv] with x hx hxv
    simpa only [hx,hxv] using hp x
  have hw := weakSpatialDerivative_of_contDiff hf z u v hu hv
  have hs := l2_square_tendsto_zero_of_ae_of_energy_le (Lp.memLp v)
    (fun n => Lp.memLp (spatialDifferenceQuotient z (h n) u)) hae (fun n => by
      rw [integral_sq_eq_bochnerL2Norm_sq (Lp.memLp _),integral_sq_eq_bochnerL2Norm_sq (Lp.memLp _),
        bochnerL2Norm_coe,bochnerL2Norm_coe]
      exact pow_le_pow_left₀ (norm_nonneg _) (hw.differenceQuotient_bound (h n)) 2)
  have he (n : ℕ) : (∫ x, (spatialDifferenceQuotient z (h n) u x-v x)^2) =
      ‖spatialDifferenceQuotient z (h n) u-v‖^2 := by
    have hm : MemLp (fun x => spatialDifferenceQuotient z (h n) u x-v x) 2 volume :=
      (Lp.memLp (spatialDifferenceQuotient z (h n) u)).sub (Lp.memLp v)
    rw [integral_sq_eq_bochnerL2Norm_sq hm]
    congr 1
    rw [← bochnerL2Norm_coe]
    exact bochnerL2Norm_congr_ae (Lp.coeFn_sub _ _).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

theorem SpatialTest.differenceQuotient_tendsto {S : Set (SpatialCoordinates d)}
    (φ : SpatialTest S) (z : SpatialCoordinates d)
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => spatialDifferenceQuotient z (h n) (φ.toLp volume)) atTop
      (𝓝 (φ.derivativeLp volume z)) :=
  spatialDifferenceQuotient_tendsto_of_contDiff (φ.smooth.of_le (by simp)) z
    (φ.toLp_ae volume) (φ.derivativeLp_ae volume z) hh ht


theorem SpatialTest.full_toLp_inner {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (φ : SpatialTest S)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ u (φ.toLp volume)=
      inner ℝ (Physical.restrictRegionLp S u) (φ.toLp (volume.restrict S)) := by
  have he : WeakSobolevJet.value φ.fullJet=φ.toLp volume :=
    Lp.ext (φ.fullJet_value_ae.trans (φ.toLp_ae volume).symm)
  simpa only [he] using φ.fullJet_inner hS u

theorem SpatialTest.full_derivativeLp_inner {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (φ : SpatialTest S) (z : SpatialCoordinates d)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ u (φ.derivativeLp volume z)=
      inner ℝ (Physical.restrictRegionLp S u) (φ.derivativeLp (volume.restrict S) z) := by
  simpa only [SpatialTest.derivativeTest_toLp] using (φ.derivativeTest z).full_toLp_inner hS u

theorem differenceQuotient_test_bound {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (z : SpatialCoordinates d)
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    {C : ℝ} (hb : ∀ᶠ n in atTop, ‖Physical.restrictRegionLp S (spatialDifferenceQuotient z (h n) u)‖ ≤ C)
    (φ : SpatialTest S) :
    |inner ℝ (Physical.restrictRegionLp S u) (φ.derivativeLp (volume.restrict S) z)| ≤
      C*‖φ.toLp (volume.restrict S)‖ := by
  have hl := (tendsto_const_nhds (x := u)).inner (𝕜 := ℝ)
    (φ.differenceQuotient_tendsto z (fun n => neg_ne_zero.mpr (hh n)) (by simpa using ht.neg))
  rw [φ.full_derivativeLp_inner hS z] at hl
  apply le_of_tendsto hl.abs
  filter_upwards [hb] with n hn
  have hi := spatialDifferenceQuotient_inner z (h n) u (φ.toLp volume)
  have he : |inner ℝ u (spatialDifferenceQuotient z (-h n) (φ.toLp volume))| =
      |inner ℝ (Physical.restrictRegionLp S (spatialDifferenceQuotient z (h n) u))
        (φ.toLp (volume.restrict S))| := by
    rw [← φ.full_toLp_inner hS]
    rw [hi,abs_neg]
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem exists_weakSpatialDerivative_of_differenceQuotient_bound
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (i : Fin d)
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ n in atTop, ‖Physical.restrictRegionLp S
      (spatialDifferenceQuotient (EuclideanSpace.basisFun (Fin d) ℝ i) (h n) u)‖ ≤ C) :
    ∃ v : Lp ℝ 2 (volume.restrict S), ‖v‖ ≤ C ∧
      IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i)
        (Physical.restrictRegionLp S u) v :=
  exists_weakSpatialDerivative_of_test_bound hS _ i hC
    (differenceQuotient_test_bound hS u _ hh ht hb)

theorem exists_weakH2_of_differenceQuotient_bounds
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (G : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hG : ∀ i, Physical.restrictRegionLp S (G i)=
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
    {h : ℕ → ℝ} (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i j : Fin d, ∀ᶠ n in atTop, ‖Physical.restrictRegionLp S
      (spatialDifferenceQuotient (EuclideanSpace.basisFun (Fin d) ℝ j) (h n) (G i))‖ ≤ C) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*C^2 := by
  apply exists_weakH2_of_gradient_test_bounds hS u hC
  intro i j φ
  rw [← hG i]
  exact differenceQuotient_test_bound hS (G i) _ hh ht (hb i j) φ

end Carleman
