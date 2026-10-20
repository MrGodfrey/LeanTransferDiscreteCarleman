module

public import Carleman.Control.CartesianWeakLimitTests

/-! The complete original Cartesian weak identity passes to the limit against actual finite smooth tests. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1200000 in
theorem cartesian_finite_test_weak_limit_identity (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ n j, h n/κ ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (ωobs : Set (SpatialCoordinates d))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    (u : ∀ n, Fin (g n).steps → CartesianPhysicalControl lo (δ n) (hδ n) (N n) ωobs)
    (y : ∀ n, Fin ((g n).steps+1) → CartesianPhysicalState (δ n) (hδ n) (N n))
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => cartesianPhysicalLaplacian lo (δ n) (hδ n) (N n)+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo (δ n) (N n) (g n)
          (cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b) i))
      (cartesianPhysicalControlExtension lo (δ n) (hδ n) (N n) ωobs) (u n) (y n))
    (Y : Lp (DirichletEnergyState (openCoordinateBox lo hi)) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)))
    (y0 : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) {CE CG CU : ℝ}
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest (openCoordinateBox lo hi))
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    let E := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ));
    let G := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ)));
    let K := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxCellControl lo hi (δ n) (hδ n) (N n) (hbox n) ωobs (u n i));
    let Yv := (dirichletStateValue (openCoordinateBox lo hi)).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient (openCoordinateBox lo hi)).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Φ := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict (openCoordinateBox lo hi)))
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φd := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict (openCoordinateBox lo hi)))
      ((continuous_time_memLp T (f l) (hf l)).toLp (f l));
    let Φg := ∑ l, timeTensor T (dirichletStateGradient (openCoordinateBox lo hi) (ψ l).dirichletState)
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φ0 := ∑ l, η l 0 • (ψ l).toLp (volume.restrict (openCoordinateBox lo hi));
    (∀ n, ‖E n‖ ≤ CE) → (∀ n, ‖G n‖ ≤ CG) → (∀ n, ‖K n‖ ≤ CU) →
    (∀ w, Tendsto (fun n => inner ℝ (E n) w) atTop (𝓝 (inner ℝ Yv w))) →
    (∀ w, Tendsto (fun n => inner ℝ (G n) w) atTop (𝓝 (inner ℝ Yg w))) →
    (∀ w, Tendsto (fun n => inner ℝ (K n) w) atTop (𝓝 (inner ℝ U w))) →
    Tendsto (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n 0)) atTop (𝓝 y0) →
    Tendsto (fun n => ‖y n (Fin.last (g n).steps)‖) atTop (𝓝 0) →
      -inner ℝ Yv Φd+inner ℝ Yg Φg+
        inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (finiteTensorTestMultiplier T η ψ hη).toL2=
      inner ℝ y0 Φ0+inner ℝ U Φ := by
  intro E G K Yv Yg Φ Φd Φg Φ0 hE hG hK hwE hwG hwK hy0 hyN
  let φ n := cartesianFiniteTestSequence lo (δ n) (hδ n) (N n) (g n) η ψ
  let V n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (φ n i.castSucc))
  let D n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      ((g n).dt⁻¹ • (φ n i.succ-φ n i.castSucc)))
  let H n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (φ n i.castSucc)))
  let P n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => (cartesianBoxReconstructedPotential lo hi (δ n) (hδ n) (N n) (hbox n) (g n)
      (cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b) i).map
        (cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ)))
  let I n := inner ℝ (cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n 0))
    (cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (φ n 0))
  let F n := inner ℝ (cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n (Fin.last (g n).steps)))
    (cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (φ n (Fin.last (g n).steps)))
  have htest := cartesian_finite_time_test_cell_L2_consistency lo hi δ hδ N hbox h hh hκ hlower hupper hlim
    T (hT 0 ▸ (g 0).period_pos.le) g hT htlim η f ψ hη hf hd
  have hV : Tendsto V atTop (𝓝 Φ) := htest.1
  have hD : Tendsto D atTop (𝓝 Φd) := by
    simpa only [D,φ,cartesianFiniteTestSequence,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one] using htest.2
  have hH : Tendsto H atTop (𝓝 Φg) := cartesian_finite_test_gradient_strong_convergence
    lo hi δ hδ N hbox h hh hκ hlower hupper hlim T g hT htlim η f ψ hη hf hd
  have hI : Tendsto I atTop (𝓝 (inner ℝ y0 Φ0)) := by
    have hs := cartesian_finite_test_endpoint_consistency lo hi δ hδ N hbox h hh hκ hlower hupper hlim η ψ 0
    simpa only [I,φ,(cartesianFiniteTestSequence_endpoints _ _ _ _ _ η ψ).1] using hy0.inner hs
  have hF : Tendsto F atTop (𝓝 0) := by
    have hz : Tendsto (fun n => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)
      (y n (Fin.last (g n).steps))) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [LinearIsometry.norm_map] using hyN
    have hs := cartesian_finite_test_endpoint_consistency lo hi δ hδ N hbox h hh hκ hlower hupper hlim η ψ T
    simpa only [F,φ,(cartesianFiniteTestSequence_endpoints _ _ _ _ _ η ψ).2,hT,inner_zero_left] using hz.inner hs
  have hpot n : inner ℝ (P n) (V n)=inner ℝ
      ((fixedSpacetimePotential T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).map
        (bochnerL2ProductIsometry (E n)))
      (cartesianFiniteTestProduct T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) η ψ) := by
    rw [← bochnerL2ProductIsometry.inner_map_map]
    dsimp only [P]
    rw [cartesian_fixed_time_product_potential]
    rfl
  have hP : Tendsto (fun n => inner ℝ (P n) (V n)) atTop
      (𝓝 (inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (finiteTensorTestMultiplier T η ψ hη).toL2)) := by
    simp_rw [hpot]
    exact cartesianAveragedPotential_weak_pairing T (hT 0 ▸ (g 0).period_pos.le) lo hi δ hδ N hN hbox g hT
      h (fun n => (hh n).le) hupper hlim htlim b (finiteTensorTestMultiplier T η ψ hη)
      (fun n => bochnerL2ProductIsometry (E n)) _ (bochnerL2ProductIsometry Yv)
      (fun n => by simpa only [LinearIsometry.norm_map] using hE n)
      (bochnerL2ProductIsometry_weak E Yv hwE)
      (cartesian_finite_test_product_strong_convergence lo hi δ hδ N hbox h hh hupper hlim T g hT htlim η f ψ hη hf hd)
  have hleft := ((hilbert_weak_strong_pairing E D Yv Φd hE hwE hD).neg.add
    (hilbert_weak_strong_pairing G H Yg Φg hG hwG hH)).add hP
  have hright := (hI.add (hilbert_weak_strong_pairing K V U Φ hK hwK hV)).sub hF
  have heq : (fun n => -inner ℝ (E n) (D n)+inner ℝ (G n) (H n)+inner ℝ (P n) (V n))=
      (fun n => I n+inner ℝ (K n) (V n)-F n) := by
    funext n
    exact cartesian_fixed_forward_reconstructed_weak_identity T lo hi (δ n) (hδ n) (N n) (hbox n)
      ωobs (g n) (hT n) (cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b)
      (u n) (y n) (φ n) (hy n)
  rw [heq] at hleft
  simpa only [sub_zero] using tendsto_nhds_unique hleft hright


end Carleman
