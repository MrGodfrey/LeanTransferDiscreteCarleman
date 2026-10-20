module
public import Carleman.Continuous.HarmonicGraphFields
public import Carleman.Continuous.TimeTraceBound
/-! Actual harmonic Bochner fields depend continuously on their two spatial coefficients. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem harmonicValue_norm_le (ω t : ℝ) (x y : H) :
    ‖harmonicValue ω x y t‖≤‖x‖+‖y‖ := by
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  exact add_le_add
    ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg x)).trans_eq (one_mul _))
    ((mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg y)).trans_eq (one_mul _))

namespace TimeGrid
variable (g : TimeGrid) (j : ℤ)

def harmonicLpLinear : (H × H) →ₗ[ℝ] Lp H 2 g.timeMeasure where
  toFun z := g.harmonicLp j z.1 z.2
  map_add' x y := by
    apply Lp.ext
    filter_upwards [g.harmonicLp_ae j (x.1+y.1) (x.2+y.2),g.harmonicLp_ae j x.1 x.2,
      g.harmonicLp_ae j y.1 y.2,Lp.coeFn_add (g.harmonicLp j x.1 x.2) (g.harmonicLp j y.1 y.2)]
      with t h1 h2 h3 h4
    simp only [Prod.fst_add,Prod.snd_add]
    rw [h1,h4]
    simp only [Pi.add_apply,h2,h3,harmonicValue,smul_add]
    module
  map_smul' c x := by
    change g.harmonicLp j (c • x.1) (c • x.2)=c • g.harmonicLp j x.1 x.2
    apply Lp.ext
    filter_upwards [g.harmonicLp_ae j (c • x.1) (c • x.2),g.harmonicLp_ae j x.1 x.2,
      Lp.coeFn_smul c (g.harmonicLp j x.1 x.2)] with t h1 h2 h3
    rw [h1,h3]
    simp only [Pi.smul_apply,h2,harmonicValue,smul_add,smul_smul]
    module

theorem harmonicLp_norm_le (x y : H) :
    ‖g.harmonicLp j x y‖≤(‖x‖+‖y‖)*Real.sqrt g.period := by
  rw [← g.timeUnit_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [g.harmonicLp_ae j x y,g.timeUnit_ae] with t ht hu
  rw [ht,hu,norm_one,mul_one]
  exact harmonicValue_norm_le _ _ x y

def harmonicLpCLM : (H × H) →L[ℝ] Lp H 2 g.timeMeasure :=
  (g.harmonicLpLinear j).mkContinuous (2*Real.sqrt g.period) (by
    intro z
    have hn := g.harmonicLp_norm_le j z.1 z.2
    have hx : ‖z.1‖≤‖z‖ := norm_fst_le z
    have hy : ‖z.2‖≤‖z‖ := norm_snd_le z
    change ‖g.harmonicLp j z.1 z.2‖≤_
    nlinarith [Real.sqrt_nonneg g.period])

theorem harmonicLp_tendsto {X Y : ℕ → H} {x y : H}
    (hX : Tendsto X atTop (𝓝 x)) (hY : Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun n => g.harmonicLp j (X n) (Y n)) atTop (𝓝 (g.harmonicLp j x y)) :=
  ((g.harmonicLpCLM j).continuous.tendsto (x,y)).comp (hX.prodMk_nhds hY)

theorem compLp_harmonic {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : H →L[ℝ] F) (x y : H) :
    L.compLp (g.harmonicLp j x y)=g.harmonicLp j (L x) (L y) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (g.harmonicLp j x y),g.harmonicLp_ae j x y,
    g.harmonicLp_ae j (L x) (L y)] with t h1 h2 h3
  rw [h1,h2,h3]
  simp only [harmonicValue,map_add,map_smul]

end TimeGrid
end Carleman
