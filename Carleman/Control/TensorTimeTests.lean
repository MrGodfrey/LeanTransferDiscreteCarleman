module

public import Carleman.Control.TimeTestSampling
public import Carleman.Control.DirichletTimeWeakCompactness

/-! Actual scalar-vector Bochner tensors, varying spatial factors, finite sums and endpoint consistency. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem bilinear_seq_tendsto
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (v : ℕ → E) (v₀ : E) (f : ℕ → F) (f₀ : F)
    (hv : Tendsto v atTop (𝓝 v₀)) (hf : Tendsto f atTop (𝓝 f₀)) :
    Tendsto (fun n => B (v n) (f n)) atTop (𝓝 (B v₀ f₀)) := by
  exact (B.continuous₂.tendsto (v₀,f₀)).comp (hv.prodMk_nhds hf)

def timeTensor (T : ℝ) : H →L[ℝ] Lp ℝ 2 (volume.restrict (Ioc 0 T)) →L[ℝ]
    Lp H 2 (volume.restrict (Ioc 0 T)) :=
  ((ContinuousLinearMap.smulRightL ℝ ℝ H) (ContinuousLinearMap.id ℝ ℝ)).compLpL₂ 2 _

theorem timeTensor_ae (T : ℝ) (v : H) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    timeTensor T v f =ᵐ[volume.restrict (Ioc 0 T)] fun t => f t • v := by
  exact (((ContinuousLinearMap.smulRightL ℝ ℝ H) (ContinuousLinearMap.id ℝ ℝ)) v).coeFn_compLp f

theorem timeTensor_reconstruction (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (v : H) (a : Fin g.steps → ℝ) :
    timeTensor T v (fixedTimeCellReconstruction T g hT a)=
      fixedTimeCellReconstruction T g hT (fun i => a i • v) := by
  exact fixedTimeCellReconstruction_map T g hT
    (((ContinuousLinearMap.smulRightL ℝ ℝ H) (ContinuousLinearMap.id ℝ ℝ)) v) a

attribute [local irreducible] timeTensor

set_option backward.isDefEq.respectTransparency true in
theorem timeTensor_strong_convergence (T : ℝ) (v : ℕ → H) (v₀ : H)
    (f : ℕ → Lp ℝ 2 (volume.restrict (Ioc 0 T))) (f₀ : Lp ℝ 2 (volume.restrict (Ioc 0 T)))
    (hv : Tendsto v atTop (𝓝 v₀)) (hf : Tendsto f atTop (𝓝 f₀)) :
    Tendsto (fun n => timeTensor T (v n) (f n)) atTop (𝓝 (timeTensor T v₀ f₀)) := by
  exact bilinear_seq_tendsto (timeTensor T) v v₀ f f₀ hv hf

theorem tensor_time_test_consistency (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (φ f : ℝ → ℝ) (hφ : ContinuousOn φ (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt φ (f t) (Icc 0 T) t)
    (v : ℕ → H) (v₀ : H) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => φ ((g n).nodeTime i) • v n))
      atTop (𝓝 (timeTensor T v₀ ((continuous_time_memLp T φ hφ).toLp φ))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => ((g n).dt⁻¹*(φ (((i.val:ℝ)+1)*(g n).dt)-φ ((i.val:ℝ)*(g n).dt))) • v n))
      atTop (𝓝 (timeTensor T v₀ ((continuous_time_memLp T f hf).toLp f))) := by
  obtain ⟨h₁,h₂⟩ := smooth_time_test_consistency T hTpos g hT htlim φ f hφ hf hd
  constructor
  · simpa only [timeTensor_reconstruction] using timeTensor_strong_convergence T v v₀ _ _ hv h₁
  · simpa only [timeTensor_reconstruction] using timeTensor_strong_convergence T v v₀ _ _ hv h₂

omit [NormedSpace ℝ H] in
theorem fixedTimeCellReconstruction_sum {ι : Type*} [Fintype ι]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T) (u : ι → Fin g.steps → H) :
    fixedTimeCellReconstruction T g hT (fun i => ∑ l, u l i)=
      ∑ l, fixedTimeCellReconstruction T g hT (u l) := by
  subst T
  change timeCellReconstruction g (fun i => ∑ l, u l i)=∑ l, timeCellReconstruction g (u l)
  apply Lp.ext
  have ha := Filter.eventually_all.mpr (fun l => timeCellReconstruction_ae g (u l))
  filter_upwards [timeCellReconstruction_ae g (fun i => ∑ l, u l i),
    Lp.coeFn_finsetSum Finset.univ (fun l => timeCellReconstruction g (u l)),ha] with t ht hs hu
  rw [ht,hs]
  simp only [Finset.sum_apply]
  simp_rw [hu]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t ∈ g.physicalTimeCell i <;> simp [hi]

theorem finite_tensor_time_test_consistency {ι : Type*} [Fintype ι]
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (φ f : ι → ℝ → ℝ) (hφ : ∀ l, ContinuousOn (φ l) (Icc 0 T))
    (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (φ l) (f l t) (Icc 0 T) t)
    (v : ι → ℕ → H) (v₀ : ι → H) (hv : ∀ l, Tendsto (v l) atTop (𝓝 (v₀ l))) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => ∑ l, φ l ((g n).nodeTime i) • v l n))
      atTop (𝓝 (∑ l, timeTensor T (v₀ l) ((continuous_time_memLp T (φ l) (hφ l)).toLp (φ l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (g n).dt⁻¹ • ((∑ l, φ l (((i.val:ℝ)+1)*(g n).dt) • v l n)-
        ∑ l, φ l ((i.val:ℝ)*(g n).dt) • v l n)))
      atTop (𝓝 (∑ l, timeTensor T (v₀ l) ((continuous_time_memLp T (f l) (hf l)).toLp (f l)))) := by
  have hh l := tensor_time_test_consistency T hTpos g hT htlim
    (φ l) (f l) (hφ l) (hf l) (hd l) (v l) (v₀ l) (hv l)
  constructor
  · simpa only [fixedTimeCellReconstruction_sum] using tendsto_finsetSum Finset.univ
      (fun l _ => (hh l).1)
  · have he n (i : Fin (g n).steps) :
        (g n).dt⁻¹ • ((∑ l, φ l (((i.val:ℝ)+1)*(g n).dt) • v l n)-
          ∑ l, φ l ((i.val:ℝ)*(g n).dt) • v l n)=
        ∑ l, ((g n).dt⁻¹*(φ l (((i.val:ℝ)+1)*(g n).dt)-φ l ((i.val:ℝ)*(g n).dt))) • v l n := by
      simp only [← Finset.sum_sub_distrib, Finset.smul_sum, ← sub_smul, smul_smul]
    simp_rw [he,fixedTimeCellReconstruction_sum]
    exact tendsto_finsetSum Finset.univ (fun l _ => (hh l).2)

theorem finite_tensor_test_endpoint_consistency {ι : Type*} [Fintype ι]
    (φ : ι → ℝ → ℝ) (v : ι → ℕ → H) (v₀ : ι → H)
    (hv : ∀ l, Tendsto (v l) atTop (𝓝 (v₀ l))) (τ : ℝ) :
    Tendsto (fun n => ∑ l, φ l τ • v l n) atTop (𝓝 (∑ l, φ l τ • v₀ l)) :=
  tendsto_finsetSum Finset.univ (fun l _ => (hv l).const_smul (φ l τ))

end Carleman
