module

public import Carleman.Control.FiniteTestPotentialConsistency
public import Carleman.Control.FixedBoxWeakTesting
public import Carleman.Control.CartesianProductL2
public import Carleman.Control.CartesianStateWeakCompactness

/-! Original full physical test sequences, fixed-domain potential transport, and actual gradient consistency. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem timeTensor_map {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (T : ℝ) (L : H →L[ℝ] G)
    (v : H) (f : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    L.compLpL 2 (volume.restrict (Ioc 0 T)) (timeTensor T v f)=timeTensor T (L v) f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (timeTensor T v f),timeTensor_ae T v f,timeTensor_ae T (L v) f] with t ht hv hg
  rw [ht,hv,hg,map_smul]

def cartesianFiniteTestSequence (lo δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (g : TimeGrid) {S : Set (SpatialCoordinates d)} {L : Type*} [Fintype L]
    (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) (i : Fin (g.steps+1)) : CartesianPhysicalState δ hδ N :=
  cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l ((i.val:ℝ)*g.dt)*(ψ l).value x)

theorem cartesianFiniteTestSequence_front (lo δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (g : TimeGrid) {S : Set (SpatialCoordinates d)} {L : Type*} [Fintype L]
    (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) (i : Fin g.steps) :
    cartesianFiniteTestSequence lo δ hδ N g η ψ i.castSucc=
      cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l (g.nodeTime i)*(ψ l).value x) := rfl

theorem cartesianFiniteTestSequence_endpoints (lo δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (g : TimeGrid) {S : Set (SpatialCoordinates d)} {L : Type*} [Fintype L]
    (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) :
    cartesianFiniteTestSequence lo δ hδ N g η ψ 0=
      cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l 0*(ψ l).value x) ∧
    cartesianFiniteTestSequence lo δ hδ N g η ψ (Fin.last g.steps)=
      cartesianNodalSample lo δ hδ N (fun x => ∑ l, η l g.period*(ψ l).value x) := by
  constructor
  · simp only [cartesianFiniteTestSequence,Fin.val_zero,Nat.cast_zero,zero_mul]
  · rfl

def cartesianGridPotential (T : ℝ) (lo hi δ : Fin d → ℝ) (N : Fin d → ℕ)
    (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j)))) := by
  have he := funext hbox
  subst hi
  subst T
  exact b

theorem cartesian_fixed_time_product_potential (T : ℝ) (lo hi δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    (u : Fin g.steps → CartesianPhysicalState δ hδ N) :
    bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT (fun i =>
      (cartesianBoxReconstructedPotential lo hi δ hδ N hbox g
        (cartesianGridPotential T lo hi δ N hbox g hT b) i).map
          (cartesianBoxCellIsometry lo hi δ hδ N hbox (u i))))=
      (fixedSpacetimePotential T lo hi δ hδ N hbox g hT b).map
        (bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
          (fun i => cartesianBoxCellIsometry lo hi δ hδ N hbox (u i)))) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesian_time_product_potential lo δ hδ N g b u

theorem cartesian_finite_test_gradient_strong_convergence (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n)
        (cartesianFiniteTestSequence lo (δ n) (hδ n) (N n) (g n) η ψ i.castSucc)))) atTop
      (𝓝 (∑ l, timeTensor T (dirichletStateGradient (openCoordinateBox lo hi) (ψ l).dirichletState) ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) := by
  have hs := (cartesian_finite_time_test_H1_consistency lo hi δ hδ N hbox h hh hκ hlower hupper hlim
    T (hT 0 ▸ (g 0).period_pos.le) g hT htlim η f ψ hη hf hd).1
  have hg := ((dirichletStateGradient (openCoordinateBox lo hi)).compLpL 2
    (volume.restrict (Ioc 0 T))).continuous.tendsto _ |>.comp hs
  simpa only [Function.comp_def,fixedTimeCellReconstruction_map,cartesianBoxDirichletState_gradient,
    _root_.map_sum,timeTensor_map,cartesianFiniteTestSequence_front] using hg

end Carleman
