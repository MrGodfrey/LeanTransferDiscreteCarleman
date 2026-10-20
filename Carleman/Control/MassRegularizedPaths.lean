module

public import Carleman.Control.MassRegularizerStrong
public import Carleman.Control.TensorAdjointPairing
public import Carleman.Continuous.WeakIntervalRepresentative

/-! Genuine continuous regularizations of a state with a weak mass derivative. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem HasWeakTimeDerivative.linear_map {g : TimeGrid} {u du : ℝ → V}
    (hw : HasWeakTimeDerivative g u du) (hu : MemLp u 2 g.timeMeasure)
    (hd : MemLp du 2 g.timeMeasure) (L : V →L[ℝ] V) :
    HasWeakTimeDerivative g (fun t => L (u t)) (fun t => L (du t)) := by
  intro φ hs hc hsup
  exact hw.map_integral hu hd L φ hs hc hsup

theorem mass_regularized_time_paths (M : V →L[ℝ] V)
    (hM : ∀ v, 0 ≤ inner ℝ (M v) v) (hdense : DenseRange M)
    {g : TimeGrid} {μ : Measure ℝ} (hμ : g.timeMeasure=μ)
    (Y D : Lp V 2 μ)
    (hw : HasWeakTimeDerivative g (M.compLpL 2 μ Y) D)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    ∃ u du : ℕ → ℝ → V,
    ∃ hu : ∀ n, MemLp (u n) 2 μ,
    ∃ hd : ∀ n, MemLp (du n) 2 μ,
      (∀ n, ContinuousOn (u n) (Icc 0 g.period)) ∧
      (∀ n, HasWeakTimeDerivative g (u n) (du n)) ∧
      (∀ n, (u n) =ᵐ[μ] (fun t => positiveMassRegularizer M hM (ε n) (hε n) (Y t))) ∧
      (∀ n, (fun t => M (du n t)) =ᵐ[μ]
        (fun t => positiveMassRegularizer M hM (ε n) (hε n) (D t))) ∧
      Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 Y) ∧
      Tendsto (fun n => ((hd n).continuousLinearMap_comp M).toLp (fun t => M (du n t)))
        atTop (𝓝 D) := by
  subst μ
  obtain ⟨m,hm,hmae,hmw⟩ := hw.exists_continuous_representative
    (Lp.memLp (M.compLpL 2 g.timeMeasure Y)) (Lp.memLp D)
  let R n := positiveMassInverse M hM (ε n) (hε n)
  let Q n := positiveMassRegularizer M hM (ε n) (hε n)
  let u n t := R n (m t)
  let du n t := R n (D t)
  have hu n : ContinuousOn (u n) (Icc 0 g.period) := (R n).continuous.comp_continuousOn hm
  have hd n : MemLp (du n) 2 g.timeMeasure := (Lp.memLp D).continuousLinearMap_comp (R n)
  have huw n : HasWeakTimeDerivative g (u n) (du n) :=
    hmw.linear_map (g.memLp_of_continuousOn hm) (Lp.memLp D) (R n)
  have huae n : u n =ᵐ[g.timeMeasure] (fun t => Q n (Y t)) := by
    filter_upwards [hmae,M.coeFn_compLpL Y] with t ht he
    change R n (m t)=M (R n (Y t))
    rw [← ht,he]
    exact positiveMassInverse_commute M hM (ε n) (hε n) (Y t)
  have hdae n : (fun t => M (du n t)) =ᵐ[g.timeMeasure] (fun t => Q n (D t)) :=
    Eventually.of_forall fun _ => rfl
  have huclass n : (g.memLp_of_continuousOn (hu n)).toLp (u n)=(Q n).compLpL 2 g.timeMeasure Y := by
    apply Lp.ext
    exact (g.memLp_of_continuousOn (hu n)).coeFn_toLp.trans ((huae n).trans ((Q n).coeFn_compLpL Y).symm)
  have hdclass n : ((hd n).continuousLinearMap_comp M).toLp (fun t => M (du n t))=
      (Q n).compLpL 2 g.timeMeasure D := by
    apply Lp.ext
    exact ((hd n).continuousLinearMap_comp M).coeFn_toLp.trans ((hdae n).trans ((Q n).coeFn_compLpL D).symm)
  have hstrong (Z : Lp V 2 g.timeMeasure) :
      Tendsto (fun n => (Q n).compLpL 2 g.timeMeasure Z) atTop (𝓝 Z) :=
    compLpL_strong_of_contractions g.timeMeasure Q
      (fun n => positiveMassRegularizer_norm M hM (ε n) (hε n))
      (positiveMassRegularizer_strong M hM hdense ε hε hlim) Z
  refine ⟨u,du,fun n => g.memLp_of_continuousOn (hu n),hd,hu,huw,huae,hdae,?_,?_⟩
  · simpa only [huclass] using hstrong Y
  · simpa only [hdclass] using hstrong D

end Carleman
