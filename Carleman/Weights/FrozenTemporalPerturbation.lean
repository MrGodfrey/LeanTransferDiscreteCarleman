module

public import Carleman.Weights.TemporalPerturbation
public import Carleman.Weights.FrozenShiftLower

/-! Uniform smallness of the actual logarithmic time derivative relative to
the frozen shift, without differentiating its half-open step coefficient. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)

/-- Choose L and the mesh threshold before T, the weight, exponent and state.
The supplied eta is an arbitrary positive absorption budget. -/
theorem logDerivative_frozen_small_uniform (m : ℕ) (hm : 0 < m)
    (β τStar η : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) (hη : 0 < η) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ u : Lp (Lp E 2 ν) 2 g.timeMeasure,
          ‖(ρ.memLp_logDerivativeAction h τ (Lp.memLp u)).toLp
            (fun t => ρ.logDerivativeAction h τ t (u t))‖ ≤
            η * ‖(s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).map u‖ := by
  let C := β*(τStar+ρ.bound)/η
  obtain ⟨L₀,δ,hL,hδ,hshift⟩ := frozen_shift_margin_uniform m hm β hβ C
  refine ⟨L₀,δ,hL,hδ,?_⟩
  intro g s w h L τ hLL hmesh hτ u
  have hc : 0 ≤ β*(τStar+ρ.bound) := by positivity [ρ.bound_nonneg]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(ρ.memLp_logDerivativeAction h τ (Lp.memLp u)).coeFn_toLp,
    (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).map_ae u,
    hshift g s w h L hLL hmesh, g.ae_mem_period] with t hd hs hlow ht
  rw [hd,hs,ρ.logDerivativeAction_eq h τ (Ioo_subset_Icc_self ht)]
  have hpow : w.q t^2 ≤ w.q t^(2*m) := pow_le_pow_right₀ (w.lower t) (by omega)
  have hcoef : β*(|τ|+ρ.bound)*w.q t^2 ≤
      η * (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t := by
    have hmul := mul_le_mul_of_nonneg_left hlow hη.le
    have he : η*(C*w.q t^(2*m)) = (β*(τStar+ρ.bound))*w.q t^(2*m) := by dsimp [C]; field_simp
    rw [he] at hmul
    have hτ' : |τ|+ρ.bound ≤ τStar+ρ.bound := by linarith
    calc
      β*(|τ|+ρ.bound)*w.q t^2 ≤ β*(τStar+ρ.bound)*w.q t^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ' hβ.le) (sq_nonneg _)
      _ ≤ β*(τStar+ρ.bound)*w.q t^(2*m) := mul_le_mul_of_nonneg_left hpow hc
      _ ≤ _ := hmul

  have hn : 0 ≤ (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t := by
    change 0 ≤ s.extension g (fun i => (L*w.nodes g i)^(2*m)) t
    cases s <;> exact (even_two_mul m).pow_nonneg _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
  exact (ρ.logDerivative_seminorm_le h τ (Ioo_subset_Icc_self ht) (u t)).trans
    ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (by ring))

end Carleman.SpatialProfile
