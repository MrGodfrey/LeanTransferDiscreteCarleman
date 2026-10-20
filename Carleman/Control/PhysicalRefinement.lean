module

public import Carleman.Control.ConformingHeatControl
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Original independent refinement gives all physical conditions and terminal norm decay. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.Physical

theorem physicalMeshScale_tendsto_atTop {κ : ℝ} (hκ : 0 < κ)
    (h dt : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hdt : ∀ n, 0 < dt n)
    (hhlim : Tendsto h atTop (𝓝 0)) (hdtlim : Tendsto dt atTop (𝓝 0)) :
    Tendsto (fun n => physicalMeshScale κ (h n) (dt n)) atTop atTop := by
  have ha := (tendsto_rpow_neg_nhdsGT_zero (y := -(4/5:ℝ)) (by norm_num)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hhlim,Eventually.of_forall hh⟩)
  have hb := (tendsto_rpow_neg_nhdsGT_zero (y := -(2/5:ℝ)) (by norm_num)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hdtlim,Eventually.of_forall hdt⟩)
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [ha.eventually (eventually_ge_atTop (a/κ)),hb.eventually (eventually_ge_atTop (a/κ))] with n hn hm
  dsimp only [Function.comp_def] at hn hm
  exact (div_le_iff₀ hκ).mp (le_min hn hm) |>.trans_eq (mul_comm _ _)

theorem physicalMeshScale_dt_bound {κ h dt : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) (hdt : 0 < dt) :
    0 ≤ dt*physicalMeshScale κ h dt ∧
      dt*physicalMeshScale κ h dt ≤ κ*dt^(3/5:ℝ) := by
  constructor
  · exact mul_nonneg hdt.le (mul_nonneg hκ (le_min (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg hdt.le _)))
  · calc
      dt*physicalMeshScale κ h dt ≤ dt*(κ*dt^(-(2/5:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hκ) hdt.le
      _ = κ*dt^(3/5:ℝ) := by
        rw [show (3/5:ℝ)=1+(-(2/5:ℝ)) by norm_num,Real.rpow_add hdt,Real.rpow_one]
        ring

theorem physicalMeshScale_dt_tendsto_zero {κ : ℝ} (hκ : 0 ≤ κ)
    (h dt : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hdt : ∀ n, 0 < dt n)
    (hdtlim : Tendsto dt atTop (𝓝 0)) :
    Tendsto (fun n => dt n*physicalMeshScale κ (h n) (dt n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (physicalMeshScale_dt_bound hκ (hh n) (hdt n)).1)
    (fun n => (physicalMeshScale_dt_bound hκ (hh n) (hdt n)).2)
  simpa using (hdtlim.rpow_const_nhds_zero (by norm_num : (0:ℝ)<3/5)).const_mul κ

theorem physical_conditions_eventually {κ h0 Δ0 qb T M : ℝ}
    (hκ : 0 < κ) (hh0 : 0 < h0) (hΔ0 : 0 < Δ0) (hqb : 0 < qb) (hT : 0 < T)
    (h dt : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hdt : ∀ n, 0 < dt n)
    (hhlim : Tendsto h atTop (𝓝 0)) (hdtlim : Tendsto dt atTop (𝓝 0)) :
    ∀ᶠ n in atTop, h n ≤ h0 ∧ dt n ≤ Δ0 ∧
      16*qb ≤ physicalMeshScale κ (h n) (dt n) ∧
      physicalMeshScale κ (h n) (dt n) ≤ qb*T/(4*dt n) ∧
      dt n*M ≤ 1/2 ∧ dt n ≤ T/12 := by
  have hs := physicalMeshScale_tendsto_atTop hκ h dt hh hdt hhlim hdtlim
  have hp := physicalMeshScale_dt_tendsto_zero hκ.le h dt hh hdt hdtlim
  have hm : Tendsto (fun n => dt n*M) atTop (𝓝 0) := by simpa using hdtlim.mul_const M
  filter_upwards [hhlim.eventually (gt_mem_nhds hh0),hdtlim.eventually (gt_mem_nhds hΔ0),
    hs.eventually (eventually_ge_atTop (16*qb)),hp.eventually (gt_mem_nhds (by positivity : 0<qb*T/4)),
    hm.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hdtlim.eventually (gt_mem_nhds (by positivity : 0<T/12))] with n hn ht hs hp hm htT
  refine ⟨hn.le,ht.le,hs,?_,hm.le,htT.le⟩
  apply (le_div_iff₀ (mul_pos (by norm_num) (hdt n))).mpr
  nlinarith

theorem physical_terminal_norm_tendsto_zero {κ d0 C Y : ℝ}
    (hκ : 0 < κ) (hd0 : 0 < d0)
    (h dt : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hdt : ∀ n, 0 < dt n)
    (hhlim : Tendsto h atTop (𝓝 0)) (hdtlim : Tendsto dt atTop (𝓝 0))
    {V : ℕ → Type*} [∀ n, SeminormedAddCommGroup (V n)] (z : ∀ n, V n)
    (hz : ∀ n, ‖z n‖ ≤ C*Real.exp (-d0*physicalMeshScale κ (h n) (dt n))*Y) :
    Tendsto (fun n => ‖z n‖) atTop (𝓝 0) := by
  have hs := physicalMeshScale_tendsto_atTop hκ h dt hh hdt hhlim hdtlim
  have he : Tendsto (fun n => Real.exp (-d0*physicalMeshScale κ (h n) (dt n))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp (hs.const_mul_atTop_of_neg (neg_neg_of_pos hd0))
  apply squeeze_zero (fun n => norm_nonneg _) hz
  simpa using (he.const_mul C).mul_const Y

end Carleman.Physical
