module

public import Carleman.Control.FiniteTensorTestMultiplier

/-! The actual finite smooth product test is the product image of its Bochner tensor. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman
variable {d : ℕ}

theorem exists_refining_time_grids (T : ℝ) (hT : 0 < T) :
    ∃ g : ℕ → TimeGrid, (∀ n, (g n).period=T) ∧ Tendsto (fun n => (g n).dt) atTop (𝓝 0) := by
  let g : ℕ → TimeGrid := fun n => ⟨n+1,by omega,T/((n:ℝ)+1),by positivity⟩
  refine ⟨g,?_,?_⟩
  · intro n
    dsimp [g,TimeGrid.period]
    push_cast
    field_simp
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul T using 1 <;>
      simp [g,div_eq_mul_inv]

theorem finiteTensorTestMultiplier_eq_product {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] (T : ℝ) (hTpos : 0 < T)
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    bochnerL2ProductIsometry (∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))=(finiteTensorTestMultiplier T η ψ hη).toL2 := by
  obtain ⟨g,hT,htlim⟩ := exists_refining_time_grids T hTpos
  let v l := (ψ l).toLp (volume.restrict S)
  let q n := bochnerL2ProductIsometry (fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => ∑ l, η l ((g n).nodeTime i) • v l))
  have hs := (finite_tensor_time_test_consistency T hTpos.le g hT htlim η f hη hf hd
    (fun l _ => v l) v (fun _ => tendsto_const_nhds)).1
  have hp := bochnerL2ProductIsometry.continuous.tendsto _ |>.comp hs
  have hq : Tendsto q atTop (𝓝 (finiteTensorTestMultiplier T η ψ hη).toL2) := by
    apply L2_tendsto_of_Linfty_error
    obtain ⟨A,B,C,D,hA,hC,hB,hD⟩ := finite_tensor_test_bounds T η f ψ hη hf hd
    have he n := bochner_finite_time_tensor_uniform_error T (g n) (hT n) η (fun l => (ψ l).value) v
      (fun l => A l) (fun l => B l) (fun _ => 0) C (fun l => (A l).coe_nonneg) hA hC
      (fun l => Eventually.of_forall (hB l))
      (fun l => by filter_upwards [(ψ l).toLp_ae (volume.restrict S)] with x hx; simp [v,hx])
      (finite_tensor_test_aestronglyMeasurable T η ψ hη)
    change Tendsto (fun n => eLpNorm (fun z => q n z-∑ l, η l z.1*(ψ l).value z.2) ⊤
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))) atTop (𝓝 0)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le) he
    have hz : Tendsto (fun n => ∑ l, ((A l:ℝ)*0+(C l:ℝ)*(g n).dt*(B l:ℝ))) atTop (𝓝 0) := by
      convert tendsto_finsetSum Finset.univ (fun l _ => (htlim.const_mul (C l:ℝ)).mul_const (B l:ℝ)) using 1 <;> simp
    simpa only [ENNReal.ofReal_zero,ENNReal.bot_eq_zero] using ENNReal.tendsto_ofReal hz
  exact tendsto_nhds_unique hp hq

end Carleman
