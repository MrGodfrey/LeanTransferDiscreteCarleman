module

public import Carleman.Control.FiniteTensorTestMultiplier

/-! Strong product limits of the original averaged potentials and full nodal tests. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def cartesianFiniteTestProduct (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi)) :
    Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))) :=
  bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
    (fun i => cartesianBoxCellIsometry lo hi δ hδ N hbox
      (cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l (g.nodeTime i)*(ψ l).value x))))

def p1FiniteTestProduct {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]
    (hS : MeasurableSet S) (T : ℝ) {ι : Type*} [Fintype ι]
    (M : SimplicialPartition S ι) (hM : M.FaceMatching) (g : TimeGrid) (hT : g.period=T)
    {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) :
    Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)) :=
  bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
    (fun i => M.nodalLp hS hM (fun x => ∑ l, η l (g.nodeTime i)*(ψ l).value x)))

theorem cartesian_finite_test_product_strong_convergence (lo hi : Fin d → ℝ)
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
    Tendsto (fun n => cartesianFiniteTestProduct T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) η ψ)
      atTop (𝓝 (finiteTensorTestMultiplier T η ψ hη).toL2) := by
  apply L2_tendsto_of_Linfty_error
  exact cartesian_finite_time_test_Linfty_consistency lo hi δ hδ N hbox h hh hstep hlim T g hT htlim η f ψ hη hf hd

theorem p1_finite_test_product_strong_convergence {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] (hS : IsOpen S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => p1FiniteTestProduct hS.measurableSet T (M n) (hM n) (g n) (hT n) η ψ)
      atTop (𝓝 (finiteTensorTestMultiplier T η ψ hη).toL2) := by
  apply L2_tendsto_of_Linfty_error
  exact p1_finite_time_test_Linfty_consistency hS M hM hlim T g hT htlim η f ψ hη hf hd

theorem cartesian_finite_test_potential_strong_convergence (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ)
    (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    Tendsto (fun n => (fixedSpacetimePotential T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).map
      (cartesianFiniteTestProduct T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) η ψ))
      atTop (𝓝 (b.map (finiteTensorTestMultiplier T η ψ hη).toL2)) := by
  exact BoundedMultiplier.test_product_strong_convergence _ b (finiteTensorTestMultiplier T η ψ hη)
    (fun n => (fixedSpacetimePotential_bound T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).le)
    (cartesianAveragedPotential_strong_convergence T (hT 0 ▸ (g 0).period_pos.le) lo hi δ hδ N hN hbox
      g hT h (fun n => (hh n).le) hstep hlim htlim b) _
    (cartesian_finite_test_product_strong_convergence lo hi δ hδ N hbox h hh hstep hlim T g hT htlim η f ψ hη hf hd)

theorem p1_finite_test_potential_strong_convergence {S : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict S)] (hS : IsOpen S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))) :
    Tendsto (fun n => (fixedTimePotential T (g n) (hT n) b).map
      (p1FiniteTestProduct hS.measurableSet T (M n) (hM n) (g n) (hT n) η ψ))
      atTop (𝓝 (b.map (finiteTensorTestMultiplier T η ψ hη).toL2)) := by
  exact BoundedMultiplier.test_product_strong_convergence _ b (finiteTensorTestMultiplier T η ψ hη)
    (fun n => (fixedTimePotential_bound T (g n) (hT n) b).le)
    (timeAveragedPotential_strong_convergence T (hT 0 ▸ (g 0).period_pos.le) g hT htlim b) _
    (p1_finite_test_product_strong_convergence hS M hM hlim T g hT htlim η f ψ hη hf hd)


end Carleman
