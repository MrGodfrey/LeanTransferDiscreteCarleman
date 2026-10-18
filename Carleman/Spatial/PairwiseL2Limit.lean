module

public import Carleman.Spatial.RealL2Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Prod

/-! Fatou passage for actual scalar L² energies and pairwise differences.
An eventual bound suffices, allowing mollifiers only after their support
has entered the original domain. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem l2_square_bound_of_ae_tendsto {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᶠ n in atTop, (∫ x, (F n x)^2 ∂ν) ≤ C) :
    (∫ x, (f x)^2 ∂ν) ≤ C := by
  have hbound : ∀ᶠ n in atTop, eLpNorm (F n) 2 ν ≤ ENNReal.ofReal (Real.sqrt C) := by
    filter_upwards [hb] with n hn
    apply (ENNReal.toReal_le_toReal (hF n).eLpNorm_lt_top.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    apply Real.le_sqrt_of_sq_le
    change (bochnerL2Norm ν (F n))^2 ≤ C
    rwa [← integral_sq_eq_bochnerL2Norm_sq (hF n)]
  have hh := Lp.eLpNorm_le_of_ae_tendsto hbound (fun n => (hF n).aestronglyMeasurable)
    hf.aestronglyMeasurable hlim
  have hn := (ENNReal.toReal_le_toReal hf.eLpNorm_lt_top.ne ENNReal.ofReal_ne_top).mpr hh
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hn
  rw [integral_sq_eq_bochnerL2Norm_sq hf]
  exact (Real.le_sqrt (bochnerL2Norm_nonneg _) hC).mp hn

theorem pairwise_memLp [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    MemLp (fun p : Ω × Ω => f p.1-f p.2) 2 (ν.prod ν) :=
  (hf.comp_fst ν).sub (hf.comp_snd ν)

theorem pairwise_integral_congr_ae {f g : Ω → ℝ} (h : f =ᵐ[ν] g) :
    (∫ x, ∫ y, (f x-f y)^2 ∂ν ∂ν)=(∫ x, ∫ y, (g x-g y)^2 ∂ν ∂ν) := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hx,hy]

theorem pairwise_square_bound_of_ae_tendsto [IsFiniteMeasure ν]
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ n in atTop, (∫ x, ∫ y, (F n x-F n y)^2 ∂ν ∂ν) ≤ C) :
    (∫ x, ∫ y, (f x-f y)^2 ∂ν ∂ν) ≤ C := by
  have hpair : ∀ᵐ p ∂ν.prod ν,
      Tendsto (fun n => F n p.1-F n p.2) atTop (𝓝 (f p.1-f p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlim,
      Measure.quasiMeasurePreserving_snd.ae hlim] with p hp hq
    exact hp.sub hq
  rw [← integral_prod _ (pairwise_memLp hf).integrable_sq]
  apply l2_square_bound_of_ae_tendsto (pairwise_memLp hf)
    (fun n => pairwise_memLp (hF n)) hpair hC
  filter_upwards [hb] with n hn
  rwa [integral_prod _ (pairwise_memLp (hF n)).integrable_sq]

theorem l2_square_bound_on_exhaustion {f : Ω → ℝ} (hf : MemLp f 2 ν)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hcover : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ A n)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, (∫ x in A n, (f x)^2 ∂ν) ≤ C) :
    (∫ x, (f x)^2 ∂ν) ≤ C := by
  have hm (n : ℕ) : MemLp ((A n).indicator f) 2 ν := hf.indicator (hA n).nullMeasurableSet
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => (A n).indicator f x) atTop (𝓝 (f x)) := by
    filter_upwards [hcover] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    exact (Set.indicator_of_mem hn f).symm
  apply l2_square_bound_of_ae_tendsto hf hm hlim hC
  apply Filter.Eventually.of_forall
  intro n
  have he : (fun x => ((A n).indicator f x)^2)=(A n).indicator (fun x => (f x)^2) := by
    funext x
    by_cases hx : x ∈ A n <;> simp [hx]
  rw [he,integral_indicator (hA n)]
  exact hb n

end Carleman
