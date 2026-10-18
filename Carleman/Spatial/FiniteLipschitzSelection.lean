module

public import Mathlib.Analysis.Calculus.MeanValue

/-! A continuous selection from finitely many equally Lipschitz real-valued
maps is Lipschitz with the same constant. This supplies the missing global
bound across the faces of a piecewise affine function. -/
@[expose] public noncomputable section
open Set Filter
open scoped Topology NNReal
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise local norm bound with one global constant controls every
segment, including across points where no derivative is available. -/
theorem lipschitzWith_of_eventually_norm_sub_le {f : E → ℝ} {C : ℝ≥0}
    (hf : Continuous f)
    (hb : ∀ x, ∀ᶠ y in 𝓝 x, ‖f y-f x‖ ≤ C*‖y-x‖) : LipschitzWith C f := by
  have hle (x y : E) : f y ≤ f x + C*‖y-x‖ := by
    let u : ℝ → ℝ := fun t => f (x+t • (y-x))
    let D : ℝ := C*‖y-x‖
    have hu : Continuous u := hf.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hh : ∀ t, ∀ᶠ z in 𝓝 t, ‖u z-u t‖ ≤ D*|z-t| := by
      intro t
      have hcont : ContinuousAt (fun z : ℝ => x+z • (y-x)) t := by fun_prop
      filter_upwards [hcont.eventually (hb (x+t • (y-x)))] with z hz
      have he : (x+z • (y-x))-(x+t • (y-x)) = (z-t) • (y-x) := by
        rw [sub_smul]; abel
      simpa only [u,he,norm_smul,Real.norm_eq_abs,mul_left_comm,mul_assoc,mul_comm,D] using hz
    have hB (t : ℝ) : HasDerivAt (fun z : ℝ => f x+D*z) D t := by
      simpa only [mul_one,zero_add,Pi.add_apply,id_eq] using! (hasDerivAt_const t (f x)).add ((hasDerivAt_id t).const_mul D)
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ r : ℝ, D < r → ∃ᶠ z in 𝓝[>] t, slope u t z < r := by
      intro t _ r hr
      apply Filter.Eventually.frequently
      filter_upwards [(hh t).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hzt
      have hpos : 0 < z-t := sub_pos.mpr hzt
      have hstep : u z-u t ≤ D*(z-t) := by
        have hn := le_trans (le_abs_self (u z-u t)) hz
        simpa only [Real.norm_eq_abs,abs_of_pos hpos] using hn
      have hs : slope u t z ≤ D := by
        rw [slope_def_field]
        exact (div_le_iff₀ hpos).mpr hstep
      exact hs.trans_lt hr
    have hres := image_le_of_liminf_slope_right_le_deriv_boundary (a := 0) (b := 1)
      hu.continuousOn (B := fun t => f x+D*t) (B' := fun _ => D)
      (by simp [u]) (by fun_prop) (fun t _ => (hB t).hasDerivWithinAt) hbound
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
    simpa only [u,one_smul,add_sub_cancel,mul_one,D] using hres
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_sub_le_iff,dist_eq_norm]
  constructor
  · have hh := hle y x
    linarith
  · have hh := hle x y
    rw [norm_sub_rev] at hh
    linarith

variable {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ E] in
theorem finite_selection_eventually_norm_sub_le {f : E → ℝ} (g : ι → E → ℝ) {C : ℝ≥0}
    (hf : Continuous f) (hg : ∀ i, LipschitzWith C (g i))
    (hselect : ∀ x, ∃ i, f x = g i x) (x : E) :
    ∀ᶠ y in 𝓝 x, ‖f y-f x‖ ≤ C*‖y-x‖ := by
  have he (i : ι) : ∀ᶠ y in 𝓝 x, f y = g i y → f x = g i x := by
    by_cases hi : f x = g i x
    · exact Eventually.of_forall (fun _ _ => hi)
    · filter_upwards [(isClosed_eq hf (hg i).continuous).isOpen_compl.mem_nhds hi] with y hy
      exact fun hh => (hy hh).elim
  filter_upwards [eventually_all.mpr he] with y hy
  obtain ⟨i,hi⟩ := hselect y
  rw [hi,hy i hi]
  exact (hg i).norm_sub_le y x

theorem lipschitzWith_finite_selection {f : E → ℝ} (g : ι → E → ℝ) {C : ℝ≥0}
    (hf : Continuous f) (hg : ∀ i, LipschitzWith C (g i))
    (hselect : ∀ x, ∃ i, f x = g i x) : LipschitzWith C f :=
  lipschitzWith_of_eventually_norm_sub_le hf (finite_selection_eventually_norm_sub_le g hf hg hselect)

end Carleman
