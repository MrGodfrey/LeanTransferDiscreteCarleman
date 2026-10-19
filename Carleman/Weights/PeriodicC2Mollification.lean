module

public import Carleman.Weights.TemporalMollificationBounds

/-! Actual smooth periodic approximations of C² weights with uniform derivative orders. -/
@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Carleman

theorem periodic_time_weight_bounds_global {q : ℝ → ℝ} {T qc β : ℝ}
    (hT : 0 < T) (hp : Function.Periodic q T)
    (hmin : ∀ t ∈ Icc 0 T, qc ≤ q t)
    (h1 : ∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2)
    (h2 : ∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) :
    ∀ t, qc ≤ q t ∧ |deriv q t| ≤ β*(q t)^2 ∧
      |deriv (deriv q) t| ≤ β^2*(q t)^3 := by
  have hp' : Function.Periodic (deriv q) T := smoothD_periodic hp 1
  have hp'' : Function.Periodic (deriv (deriv q)) T := smoothD_periodic hp' 1
  have htuple : Function.Periodic (fun t => (q t,deriv q t,deriv (deriv q) t)) T := by
    intro t
    simp only [hp t,hp' t,hp'' t]
  intro t
  obtain ⟨s,hs,he⟩ := htuple.exists_mem_Ico₀ hT t
  have hq := congrArg Prod.fst he
  have hdq := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) he
  have hddq := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) he
  dsimp only at hq hdq hddq
  rw [hq,hdq,hddq]
  exact ⟨hmin s (Ico_subset_Icc_self hs),h1 s (Ico_subset_Icc_self hs),h2 s (Ico_subset_Icc_self hs)⟩

theorem temporalMollification_qclass {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q)
    {T qc β D : ℝ} (hT : 0 < T) (hp : Function.Periodic q T)
    (hqc : 0 < qc) (hβ : 0 ≤ β) (hmin : ∀ t, qc ≤ q t)
    (h1 : ∀ t, |deriv q t| ≤ β*(q t)^2)
    (h2 : ∀ t, |deriv (deriv q) t| ≤ β^2*(q t)^3)
    (hD0 : 0 ≤ D) (hD : ∀ t, |deriv q t| ≤ D)
    (n : ℕ) (hn : D*(temporalBump n).rOut ≤ qc/2) :
    ∀ t, qc ≤ temporalMollification q n t ∧
      |deriv (temporalMollification q n) t| ≤ (9*β)*(temporalMollification q n t)^2 ∧
      |deriv (deriv (temporalMollification q n)) t| ≤ (27*β^2)*(temporalMollification q n t)^3 := by
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  obtain ⟨B,_hB,hbound⟩ := continuous_periodic_bounded hq.continuous hT hp
  have hupper : ∀ t, q t ≤ B := fun t => (le_abs_self _).trans (hbound t)
  intro t
  have hlow := (temporalMollification_bounds hq.continuous hmin hupper n t).1
  have hqn : 0 ≤ temporalMollification q n t := hqc.le.trans hlow
  refine ⟨hlow,?_,?_⟩
  · rw [temporalMollification_deriv_periodic hq1 hT hp]
    apply temporalMollification_local_norm_bound
    intro s hs
    have hcomp := temporalMollification_support_comparison hq1 hD0 hD hmin n hn t s hs
    have hpow := pow_le_pow_left₀ (hqc.le.trans (hmin (t-s))) hcomp 2
    have hh := mul_le_mul_of_nonneg_left hpow hβ
    nlinarith [h1 (t-s)]
  · rw [temporalMollification_second_deriv_periodic hq hT hp]
    apply temporalMollification_local_norm_bound
    intro s hs
    have hcomp := temporalMollification_support_comparison hq1 hD0 hD hmin n hn t s hs
    have hpow := pow_le_pow_left₀ (hqc.le.trans (hmin (t-s))) hcomp 3
    have hh := mul_le_mul_of_nonneg_left hpow (sq_nonneg β)
    nlinarith [h2 (t-s)]

theorem exists_periodic_C2_smooth_qclass {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q)
    {T qc β : ℝ} (hT : 0 < T) (hp : Function.Periodic q T) (hqc : 0 < qc) (hβ : 0 ≤ β)
    (hmin : ∀ t ∈ Icc 0 T, qc ≤ q t)
    (h1 : ∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2)
    (h2 : ∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) :
    ∃ B : ℝ, 0 < B ∧ ∃ qs : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (qs n) ∧ Function.Periodic (qs n) T ∧
      ∀ t, qc ≤ qs n t ∧ qs n t ≤ B ∧ |deriv (qs n) t| ≤ (9*β)*(qs n t)^2 ∧
        |deriv (deriv (qs n)) t| ≤ (27*β^2)*(qs n t)^3) ∧
      (∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t))) := by
  have hg := periodic_time_weight_bounds_global hT hp hmin h1 h2
  obtain ⟨B,hB,hupper⟩ := continuous_periodic_bounded hq.continuous hT hp
  have hp' : Function.Periodic (deriv q) T := smoothD_periodic hp 1
  obtain ⟨D,hD,hbound⟩ := continuous_periodic_bounded (hq.continuous_deriv (by norm_num)) hT hp'
  have htend := temporalBump_radius_tendsto.const_mul D
  have hev : ∀ᶠ n in atTop, D*(temporalBump n).rOut ≤ qc/2 := by
    have hh := htend.eventually (gt_mem_nhds (show D*0 < qc/2 by nlinarith))
    exact hh.mono fun _ h => h.le
  obtain ⟨N,hN⟩ := eventually_atTop.1 hev
  refine ⟨B,hB,fun n => temporalMollification q (n+N),?_,?_⟩
  · intro n
    refine ⟨temporalMollification_smooth hq.continuous _,temporalMollification_periodic hp _,?_⟩
    intro t
    have hh := temporalMollification_qclass hq hT hp hqc hβ (fun t => (hg t).1)
      (fun t => (hg t).2.1) (fun t => (hg t).2.2) hD.le hbound (n+N) (hN _ (by omega)) t
    exact ⟨hh.1,(temporalMollification_bounds hq.continuous (fun s => (hg s).1)
      (fun s => (le_abs_self _).trans (hupper s)) (n+N) t).2,hh.2⟩
  · intro t
    exact (temporalMollification_tendsto hq.continuous t).comp (tendsto_add_atTop_nat N)

theorem exists_periodic_C2_smooth_qclass_exact {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q)
    {T qc β : ℝ} (hT : 0 < T) (hp : Function.Periodic q T) (hqc : 0 < qc) (hβ : 0 ≤ β)
    (hmin : ∀ t ∈ Icc 0 T, qc ≤ q t)
    (h1 : ∀ t ∈ Icc 0 T, |deriv q t| ≤ (β/9)*(q t)^2)
    (h2 : ∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ (β/9)^2*(q t)^3) :
    ∃ B : ℝ, 0 < B ∧ ∃ qs : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (qs n) ∧ Function.Periodic (qs n) T ∧
      ∀ t, qc ≤ qs n t ∧ qs n t ≤ B ∧ |deriv (qs n) t| ≤ β*(qs n t)^2 ∧
        |deriv (deriv (qs n)) t| ≤ β^2*(qs n t)^3) ∧
      (∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t))) := by
  obtain ⟨B,hB,qs,hqs,htend⟩ := exists_periodic_C2_smooth_qclass hq hT hp hqc
    (div_nonneg hβ (by norm_num)) hmin h1 h2
  refine ⟨B,hB,qs,?_,htend⟩
  intro n
  refine ⟨(hqs n).1,(hqs n).2.1,?_⟩
  intro t
  obtain ⟨hl,hu,hf,hs⟩ := (hqs n).2.2 t
  refine ⟨hl,hu,?_,?_⟩
  · nlinarith
  · have hn : 0 ≤ qs n t := hqc.le.trans hl
    have hh : 0 ≤ β^2*(qs n t)^3 := mul_nonneg (sq_nonneg β) (pow_nonneg hn _)
    nlinarith

end Carleman
