module

public import Carleman.Spatial.CutoffPoissonConvolution
public import Carleman.Spatial.MollifiedInterpolation
public import Carleman.Spatial.L2BoundedMultiplierLimit
public import Carleman.Continuous.BochnerNormAlgebra

/-! Uniform L² bounds for the actual localized Laplacian. The constant is
chosen from the fixed smooth cutoff before the kernel and the weak solution. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.exists_laplacian_multiplier_bound (η : SpatialTest S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |η.value x| ≤ M ∧
      (∀ i : Fin d, |fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i)| ≤ M) ∧
      |spatialLaplacian η.value x| ≤ M := by
  obtain ⟨A,hA⟩ := η.compact.exists_bound_of_continuous η.smooth.continuous
  have hg (i : Fin d) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i)| ≤ B := by
    obtain ⟨B,hB⟩ := (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).compact.exists_bound_of_continuous
      (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).smooth.continuous
    exact ⟨max 0 B,le_max_left _ _,fun x => (hB x).trans (le_max_right _ _)⟩
  choose B hB hg using hg
  obtain ⟨D,hD⟩ := η.compact.exists_bound_of_continuousOn (spatialLaplacian_smooth η.smooth).continuous.continuousOn
  have hsum : 0 ≤ ∑ i : Fin d, B i := Finset.sum_nonneg fun i _ => hB i
  refine ⟨max 0 A + (∑ i : Fin d, B i) + max 0 D,by positivity,?_⟩
  intro x
  refine ⟨?_,?_,?_⟩
  · have ha := (hA x).trans (le_max_right 0 A)
    change |η.value x| ≤ max 0 A at ha
    linarith [le_max_left 0 D]
  · intro i
    have hb : B i ≤ ∑ j : Fin d, B j := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
    exact (hg i x).trans (by linarith [le_max_left 0 A,le_max_left 0 D])
  · by_cases hx : x ∈ tsupport η.value
    · have hd := (hD x hx).trans (le_max_right 0 D)
      change |spatialLaplacian η.value x| ≤ max 0 D at hd
      linarith [le_max_left 0 A]
    · rw [η.laplacian_eq_zero_of_notMem_tsupport hx,abs_zero]
      positivity

set_option maxHeartbeats 800000 in
theorem IsWeakNegativeLaplacian.cutoff_laplacian_bound (hS : MeasurableSet S)
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakNegativeLaplacian u f) (η : SpatialTest S)
    {M : ℝ} (hM : 0 ≤ M)
    (hη : ∀ x, |η.value x| ≤ M)
    (hgrad : ∀ i : Fin d, ∀ x, |fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i)| ≤ M)
    (hlap : ∀ x, |spatialLaplacian η.value x| ≤ M)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ tsupport η.value, ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    let φ := η.mulSmooth (κ.smooth_convolution (zeroExtendLp hS (WeakSobolevJet.value u)));
    ‖φ.laplacianLp‖ ≤ M*(‖f‖ +
      2*(∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) +
      ‖WeakSobolevJet.value u‖) := by
  intro φ
  let conv (v : Lp ℝ 2 (volume.restrict S)) :=
    zeroExtendLp hS v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hc (v : Lp ℝ 2 (volume.restrict S)) : MemLp (conv v) 2 (volume.restrict S) ∧
      bochnerL2Norm (volume.restrict S) (conv v) ≤ ‖v‖ := by
    have hh := κ.convolution_right_memLp_norm_le hκ hunit (zeroExtendLp hS v)
    refine ⟨hh.1.mono_measure Measure.restrict_le_self,?_⟩
    have hm : bochnerL2Norm (volume.restrict S) (conv v) ≤ bochnerL2Norm volume (conv v) :=
      ENNReal.toReal_mono hh.1.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)
    rw [zeroExtendLp_norm] at hh
    exact hm.trans hh.2
  let A := fun x => η.value x*conv f x
  let G (i : Fin d) := fun x => (fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i))*
    conv (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) x
  let B := fun x => ∑ i : Fin d, G i x
  let D := fun x => spatialLaplacian η.value x*conv (WeakSobolevJet.value u) x
  have hA : MemLp A 2 (volume.restrict S) := memLp_mul_of_ae_bound
    η.smooth.continuous.aestronglyMeasurable (hc f).1 hM (Filter.Eventually.of_forall hη)
  have hG (i : Fin d) : MemLp (G i) 2 (volume.restrict S) := memLp_mul_of_ae_bound
    (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).smooth.continuous.aestronglyMeasurable
    (hc _).1 hM (Filter.Eventually.of_forall (hgrad i))
  have hB : MemLp B 2 (volume.restrict S) := memLp_finsetSum _ (fun i _ => hG i)
  have hD : MemLp D 2 (volume.restrict S) := memLp_mul_of_ae_bound
    (spatialLaplacian_smooth η.smooth).continuous.aestronglyMeasurable (hc _).1 hM
    (Filter.Eventually.of_forall hlap)
  have hAn : bochnerL2Norm (volume.restrict S) A ≤ M*‖f‖ :=
    (bochnerL2Norm_mul_le_of_ae_bound η.smooth.continuous.aestronglyMeasurable
      (hc f).1 hM (Filter.Eventually.of_forall hη)).trans (mul_le_mul_of_nonneg_left (hc f).2 hM)
  have hGn (i : Fin d) : bochnerL2Norm (volume.restrict S) (G i) ≤
      M*‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖ :=
    (bochnerL2Norm_mul_le_of_ae_bound
      (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).smooth.continuous.aestronglyMeasurable
      (hc _).1 hM (Filter.Eventually.of_forall (hgrad i))).trans (mul_le_mul_of_nonneg_left (hc _).2 hM)
  have hBn : bochnerL2Norm (volume.restrict S) B ≤
      M*(∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) := by
    exact (bochnerL2Norm_finsetSum Finset.univ G (fun i _ => hG i)).trans
      (by simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hGn i))
  have hDn : bochnerL2Norm (volume.restrict S) D ≤ M*‖WeakSobolevJet.value u‖ :=
    (bochnerL2Norm_mul_le_of_ae_bound (spatialLaplacian_smooth η.smooth).continuous.aestronglyMeasurable
      (hc _).1 hM (Filter.Eventually.of_forall hlap)).trans (mul_le_mul_of_nonneg_left (hc _).2 hM)
  have he : φ.laplacianLp =ᵐ[volume.restrict S] (fun x => -A x+2*B x+D x) := by
    filter_upwards [φ.laplacianLp_ae] with x hx
    rw [hx]
    change spatialLaplacian (fun y => η.value y*conv (WeakSobolevJet.value u) y) x =
      -(η.value x*conv f x) + 2*(∑ i : Fin d, (fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i))*
        conv (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)) x) +
      spatialLaplacian η.value x*conv (WeakSobolevJet.value u) x
    rw [← neg_mul]
    exact h.cutoff_convolution hS η κ hinside x
  have hn : ‖φ.laplacianLp‖ = bochnerL2Norm (volume.restrict S) (fun x => -A x+2*B x+D x) := by
    rw [← bochnerL2Norm_congr_ae he,bochnerL2Norm_eq _ (Lp.memLp _),Lp.toLp_coeFn]
  rw [hn]
  have hh := (bochnerL2Norm_add (hA.neg.add (hB.const_mul 2)) hD).trans
    (add_le_add (bochnerL2Norm_add hA.neg (hB.const_mul 2)) le_rfl)
  change bochnerL2Norm (volume.restrict S) (fun x => -A x+2*B x+D x) ≤
    bochnerL2Norm (volume.restrict S) (-A) + bochnerL2Norm (volume.restrict S) ((2:ℝ) • B) +
    bochnerL2Norm (volume.restrict S) D at hh
  rw [bochnerL2Norm_neg,bochnerL2Norm_const_smul] at hh
  norm_num at hh
  nlinarith


theorem exists_uniform_cutoff_H2 (hS : IsOpen S) (η : SpatialTest S) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S)),
      IsWeakNegativeLaplacian u f →
      ∀ (κ : SpatialTest (univ : Set (SpatialCoordinates d))),
      (∀ x, 0 ≤ κ.value x) → (∫ x, κ.value x = 1) →
      (∀ x ∈ tsupport η.value, ∀ y ∈ tsupport κ.value, x-y ∈ S) →
      let φ := η.mulSmooth (κ.smooth_convolution (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)));
      ∃ v : WeakSobolevJet d 2 (volume.restrict S) S,
        WeakSobolevJet.truncate (by decide : 1 ≤ 2) v = φ.sobolevJet ∧
        negativeLaplacian v = -φ.laplacianLp ∧
        ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*
          (M*(‖f‖ + 2*(∑ i : Fin d,
            ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) +
            ‖WeakSobolevJet.value u‖))^2 := by
  obtain ⟨M,hM,hb⟩ := η.exists_laplacian_multiplier_bound
  refine ⟨M,hM,?_⟩
  intro u f hu κ hκ hunit hinside φ
  obtain ⟨v,hv,hl,hn⟩ := φ.exists_H2_jet hS
  refine ⟨v,hv,hl,hn.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
  exact hu.cutoff_laplacian_bound hS.measurableSet η hM
    (fun x => (hb x).1) (fun i x => (hb x).2.1 i) (fun x => (hb x).2.2) κ hκ hunit hinside

end Carleman
