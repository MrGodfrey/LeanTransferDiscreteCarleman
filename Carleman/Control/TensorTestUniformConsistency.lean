module

public import Carleman.Control.TensorTestUniformError

/-! The original P1 and Cartesian sampled tests converge in product L-infinity, with independent mesh limits. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem cartesian_finite_time_test_uniform_bound (lo hi : Fin d → ℝ)
    (T : ℝ) {L : Type*} [Fintype L] (η f : L → ℝ → ℝ)
    (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
      (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
      (g : TimeGrid) (hT : g.period=T) (h : ℝ), 0 < h → (∀ j, δ j ≤ h) →
      eLpNorm (fun z => bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
        (fun i => cartesianBoxCellIsometry lo hi δ hδ N hbox
          (cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l (g.nodeTime i)*(ψ l).value x)))) z-
        ∑ l, η l z.1*(ψ l).value z.2) ⊤
          ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))
        ≤ ENNReal.ofReal (A*h+B*g.dt) := by
  obtain ⟨A,B,C,D,hA,hC,hB,hD⟩ := finite_tensor_test_bounds T η f ψ hη hf hd
  refine ⟨∑ l, (A l:ℝ)*D l*(d+1:ℝ),∑ l, (C l:ℝ)*B l,by positivity,by positivity,?_⟩
  intro δ hδ N hbox g hT h hh hstep
  let v l := cartesianBoxCellIsometry lo hi δ hδ N hbox (cartesianNodalSample lo δ hδ N (ψ l).value)
  have hv l : ∀ᵐ x ∂volume.restrict (openCoordinateBox lo hi), |v l x-(ψ l).value x| ≤ D l*(d+1:ℝ)*h := by
    filter_upwards [finiteCellLinear_ae (ν := volume.restrict (openCoordinateBox lo hi))
      (cartesianDualCell lo δ N) (cartesianDualCell_measurable lo δ N)
      (Finset.prod_pos (fun j _ => hδ j)) (cartesianNodalSample lo δ hδ N (ψ l).value),
      cartesian_box_test_cell_uniform_error lo hi δ hδ N hbox (ψ l) (hD l) h hh hstep] with x hx he
    change v l x=finiteCellFunction _ _ x at hx
    simpa only [hx] using he
  simp_rw [cartesianNodalSample_finite,_root_.map_sum,map_smul]
  have he := bochner_finite_time_tensor_uniform_error T g hT η (fun l => (ψ l).value) v
    (fun l => A l) (fun l => B l) (fun l => D l*(d+1:ℝ)*h) C (fun l => (A l).coe_nonneg)
    hA hC (fun l => Filter.Eventually.of_forall (hB l)) hv
    (finite_tensor_test_aestronglyMeasurable T η ψ hη)
  convert he using 1
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem SimplicialPartition.nodalLp_finite {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] {ι L : Type*} [Fintype ι] [Fintype L]
    (M : SimplicialPartition S ι) (hS : MeasurableSet S) (hM : M.FaceMatching)
    (ψ : L → SpatialCoordinates d → ℝ) (c : L → ℝ) :
    M.nodalLp hS hM (fun x => ∑ l, c l*ψ l x)=∑ l, c l • M.nodalLp hS hM (ψ l) := by
  have he : (fun x => ∑ l, c l*ψ l x)=∑ l, c l • ψ l := by
    funext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  change M.nodalLpLinearMap hS hM (∑ l, c l • ψ l)=_
  simp only [_root_.map_sum,map_smul]
  rfl

theorem p1_finite_time_test_uniform_bound {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] (hS : IsOpen S)
    (T : ℝ) {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {ι : Type*} [Fintype ι]
      (M : SimplicialPartition S ι) (hM : M.FaceMatching) (g : TimeGrid) (hT : g.period=T),
      eLpNorm (fun z => bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
        (fun i => M.nodalLp hS.measurableSet hM (fun x => ∑ l, η l (g.nodeTime i)*(ψ l).value x))) z-
        ∑ l, η l z.1*(ψ l).value z.2) ⊤ ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))
        ≤ ENNReal.ofReal (A*M.maxDiameter+B*g.dt) := by
  obtain ⟨A,B,C,D,hA,hC,hB,hD⟩ := finite_tensor_test_bounds T η f ψ hη hf hd
  refine ⟨∑ l, (A l:ℝ)*2*D l,∑ l, (C l:ℝ)*B l,by positivity,by positivity,?_⟩
  intro ι _ M hM g hT
  let v l := M.nodalLp hS.measurableSet hM (ψ l).value
  have hv l : ∀ᵐ x ∂volume.restrict S, |v l x-(ψ l).value x| ≤ 2*D l*M.maxDiameter := by
    filter_upwards [M.nodalLp_ae hS.measurableSet hM (ψ l).value,
      p1_test_uniform_error hS M hM (ψ l) (hD l)] with x hx he
    simpa only [show v l x=M.nodalFunction (ψ l).value x from hx] using he
  simp_rw [M.nodalLp_finite]
  have he := bochner_finite_time_tensor_uniform_error T g hT η (fun l => (ψ l).value) v
    (fun l => A l) (fun l => B l) (fun l => 2*D l*M.maxDiameter) C (fun l => (A l).coe_nonneg)
    hA hC (fun l => Filter.Eventually.of_forall (hB l)) hv
    (finite_tensor_test_aestronglyMeasurable T η ψ hη)
  convert he using 1
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring


theorem cartesian_finite_time_test_Linfty_consistency (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ)
    (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => eLpNorm (fun z => bochnerL2ProductIsometry
      (fixedTimeCellReconstruction T (g n) (hT n)
        (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
          (cartesianNodalSample lo (δ n) (hδ n) (N n)
            (fun x => ∑ l, η l ((g n).nodeTime i)*(ψ l).value x)))) z-
        ∑ l, η l z.1*(ψ l).value z.2) ⊤
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) atTop (𝓝 0) := by
  obtain ⟨A,B,_,_,he⟩ := cartesian_finite_time_test_uniform_bound lo hi T η f ψ hη hf hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le) (fun n => he (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) (h n) (hh n) (hstep n))
  simpa only [mul_zero,add_zero,ENNReal.ofReal_zero,ENNReal.bot_eq_zero] using
    ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul hlim).add (tendsto_const_nhds.mul htlim))

theorem p1_finite_time_test_Linfty_consistency {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] (hS : IsOpen S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => eLpNorm (fun z => bochnerL2ProductIsometry
      (fixedTimeCellReconstruction T (g n) (hT n)
        (fun i => (M n).nodalLp hS.measurableSet (hM n)
          (fun x => ∑ l, η l ((g n).nodeTime i)*(ψ l).value x))) z-
        ∑ l, η l z.1*(ψ l).value z.2) ⊤
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))) atTop (𝓝 0) := by
  obtain ⟨A,B,_,_,he⟩ := p1_finite_time_test_uniform_bound hS T η f ψ hη hf hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le) (fun n => he (M n) (hM n) (g n) (hT n))
  simpa only [mul_zero,add_zero,ENNReal.ofReal_zero,ENNReal.bot_eq_zero] using
    ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul hlim).add (tendsto_const_nhds.mul htlim))


end Carleman
