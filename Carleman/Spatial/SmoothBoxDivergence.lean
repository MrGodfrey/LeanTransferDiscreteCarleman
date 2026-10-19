module

public import Carleman.Geometry.ClosedCoordinateFaces
public import Carleman.Spatial.SmoothDirectionalCalculus
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! The actual Euclidean divergence theorem on coordinate boxes.
Face integrals use the standard coordinate parametrizations and Lebesgue measure. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def coordinateDivergence (F : Fin d → SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (F i) x

theorem coordinateDivergence_contDiff {F : Fin d → SpatialCoordinates d → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) : ContDiff ℝ ∞ (coordinateDivergence F) :=
  ContDiff.sum fun i _ => smoothD_contDiff (hF i) _

theorem smooth_closed_box_divergence (a b : Fin (d+1) → ℝ) (hab : ∀ i, a i ≤ b i)
    {F : Fin (d+1) → SpatialCoordinates (d+1) → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    (∫ x in closedCoordinateBox a b, coordinateDivergence F x) =
      ∑ i : Fin (d+1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F i (WithLp.toLp 2 (i.insertNth (b i) y))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F i (WithLp.toLp 2 (i.insertNth (a i) y))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) => ℝ)).symm
  let g : Fin (d+1) → (Fin (d+1) → ℝ) → ℝ := fun i x => F i (e x)
  let g' : Fin (d+1) → (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ) →L[ℝ] ℝ :=
    fun i x => (fderiv ℝ (F i) (e x)).comp e.toContinuousLinearMap
  have hd i x : HasFDerivAt (g i) (g' i x) x :=
    ((hF i).differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt
  have he x : (∑ i, g' i x (Pi.single i 1))=coordinateDivergence F (e x) := by
    apply Finset.sum_congr rfl
    intro i _
    have hb : e (Pi.single i 1)=EuclideanSpace.basisFun (Fin (d+1)) ℝ i := by
      apply PiLp.ext
      intro j
      simp [e,EuclideanSpace.basisFun_apply]
    change (fderiv ℝ (F i) (e x)) (e (Pi.single i 1)) =
      (fderiv ℝ (F i) (e x)) (EuclideanSpace.basisFun (Fin (d+1)) ℝ i)
    rw [hb]
  have hc : Continuous (fun x => coordinateDivergence F (e x)) :=
    (coordinateDivergence_contDiff hF).continuous.comp e.continuous
  have hi : IntegrableOn (fun x => ∑ i, g' i x (Pi.single i 1)) (Icc a b) := by
    simpa only [he] using hc.integrableOn_Icc (a := a) (b := b)
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab g g' ∅ countable_empty
    (fun i => ((hF i).continuous.comp e.continuous).continuousOn) (fun x _ i => hd i x) hi
  have hs : e ⁻¹' closedCoordinateBox a b=Icc a b := by
    ext x
    simp only [mem_preimage,closedCoordinateBox,mem_ofPred_eq,mem_Icc,Pi.le_def]
    exact forall_and
  have hm := (PiLp.volume_preserving_toLp (Fin (d+1))).setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (coordinateDivergence F) (closedCoordinateBox a b)
  change (∫ x in e ⁻¹' closedCoordinateBox a b, coordinateDivergence F (e x))=_ at hm
  rw [hs] at hm
  rw [← hm]
  simp_rw [he] at h
  exact h

theorem openCoordinateBox_ae_closed (a b : Fin d → ℝ) :
    openCoordinateBox a b =ᵐ[volume] closedCoordinateBox a b := by
  have h : (Set.pi univ (fun i => Ioo (a i) (b i))) =ᵐ[volume] Icc a b := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  have hh := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae h
  filter_upwards [hh] with x hx
  simpa only [mem_pi,mem_univ,true_implies,mem_Ioo,mem_Icc,Pi.le_def,
    openCoordinateBox,closedCoordinateBox,mem_ofPred_eq,forall_and] using hx

theorem smooth_open_box_divergence (a b : Fin (d+1) → ℝ) (hab : ∀ i, a i ≤ b i)
    {F : Fin (d+1) → SpatialCoordinates (d+1) → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    (∫ x in openCoordinateBox a b, coordinateDivergence F x) =
      ∑ i : Fin (d+1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F i (WithLp.toLp 2 (i.insertNth (b i) y))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F i (WithLp.toLp 2 (i.insertNth (a i) y))) := by
  rw [setIntegral_congr_set (openCoordinateBox_ae_closed a b)]
  exact smooth_closed_box_divergence a b hab hF

end Carleman
