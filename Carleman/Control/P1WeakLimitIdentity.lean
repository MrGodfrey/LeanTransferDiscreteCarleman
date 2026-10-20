module

public import Carleman.Control.P1FiniteTestConsistency
public import Carleman.Control.TimeAveragedProductPotential
public import Carleman.Control.ConformingWeakTesting
public import Carleman.Control.FiniteTensorProductIdentity

/-! All six terms of the original P1 equation converge to the same original weak identity. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]

theorem full_p1_finite_test_weak_limit_identity (hS : IsOpen S) (hc : Convex ℝ S)
    (hdim : 0 < d) (hSb : Bornology.IsBounded S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (mesh : ∀ n, SimplicialPartition S (ι n))
    (hmesh : ∀ n, (mesh n).FaceMatching) (hboundary : ∀ n, (mesh n).BoundaryFitted)
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (mesh n).cell i)
    (hshape : ∀ n i, (mesh n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (mesh n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (ω : Set (SpatialCoordinates d))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (u : ∀ n, Fin (g n).steps → Lp ℝ 2 ((volume.restrict S).restrict ω))
    (y : ∀ n, Fin ((g n).steps+1) → (mesh n).conformingSpace (dirichletSubspace S))
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hdim hSb)
        ((mesh n).conformingSpace (dirichletSubspace S)) ((mesh n).conformingSpace_le (dirichletSubspace S))+
        Physical.conformingPotential ((mesh n).conformingSpace (dirichletSubspace S))
          (fixedTimeCellPotential T (g n) (hT n) b i))
      (Physical.conformingRegionControl ((mesh n).conformingSpace (dirichletSubspace S)) ω) (u n) (y n))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (y0 : Lp ℝ 2 (volume.restrict S)) {CE CG CU : ℝ}
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    let R := fun n => dirichletGalerkinState hS hdim hSb
      ((mesh n).conformingSpace (dirichletSubspace S)) ((mesh n).conformingSpace_le (dirichletSubspace S));
    let E := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (y n i.succ : Lp ℝ 2 (volume.restrict S)));
    let G := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => dirichletStateGradient S (R n (y n i.succ)));
    let K := fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (Physical.restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i));
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Φ := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φd := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
      ((continuous_time_memLp T (f l) (hf l)).toLp (f l));
    let Φg := ∑ l, timeTensor T (dirichletStateGradient S (ψ l).dirichletState)
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φ0 := ∑ l, η l 0 • (ψ l).toLp (volume.restrict S);
    (∀ n, ‖E n‖ ≤ CE) → (∀ n, ‖G n‖ ≤ CG) → (∀ n, ‖K n‖ ≤ CU) →
    (∀ w, Tendsto (fun n => inner ℝ (E n) w) atTop (𝓝 (inner ℝ Yv w))) →
    (∀ w, Tendsto (fun n => inner ℝ (G n) w) atTop (𝓝 (inner ℝ Yg w))) →
    (∀ w, Tendsto (fun n => inner ℝ (K n) w) atTop (𝓝 (inner ℝ U w))) →
    Tendsto (fun n => (y n 0 : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 y0) →
    Tendsto (fun n => ‖y n (Fin.last (g n).steps)‖) atTop (𝓝 0) →
      -inner ℝ Yv Φd+inner ℝ Yg Φg+
        inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (finiteTensorTestMultiplier T η ψ hη).toL2=
      inner ℝ y0 Φ0+inner ℝ U Φ := by
  intro R E G K Yv Yg Φ Φd Φg Φ0 hE hG hK hwE hwG hwK hy0 hyN
  let φ n := p1FiniteTestSequence (mesh n) hS hc (hmesh n) (hboundary n) (g n) η ψ
  let V n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => (φ n i.castSucc : Lp ℝ 2 (volume.restrict S)))
  let D n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => ((g n).dt⁻¹ • (φ n i.succ-φ n i.castSucc) : Lp ℝ 2 (volume.restrict S)))
  let H n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => dirichletStateGradient S (R n (φ n i.castSucc)))
  let P n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => (fixedTimeCellPotential T (g n) (hT n) b i).map (y n i.succ : Lp ℝ 2 (volume.restrict S)))
  let I n := inner ℝ (y n 0 : Lp ℝ 2 (volume.restrict S)) (φ n 0 : Lp ℝ 2 (volume.restrict S))
  let F n := inner ℝ (y n (Fin.last (g n).steps) : Lp ℝ 2 (volume.restrict S))
    (φ n (Fin.last (g n).steps) : Lp ℝ 2 (volume.restrict S))
  have htpos : 0 < T := hT 0 ▸ (g 0).period_pos
  have htest := full_p1_galerkin_finite_time_test_consistency hS hc hdim hSb mesh hmesh hboundary
    hκ a r hr hball hshape hlim T htpos.le g hT htlim η f ψ hη hf hd
  have hV : Tendsto V atTop (𝓝 Φ) := htest.1
  have hD : Tendsto D atTop (𝓝 Φd) := htest.2.1
  have hH : Tendsto H atTop (𝓝 Φg) := htest.2.2
  have hep := full_p1_galerkin_finite_test_endpoint_consistency hS hc mesh hmesh hboundary hlim T g hT η ψ
  have hI : Tendsto I atTop (𝓝 (inner ℝ y0 Φ0)) := hy0.inner hep.1
  have hF : Tendsto F atTop (𝓝 0) := by
    have hz : Tendsto (fun n => (y n (Fin.last (g n).steps) : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact hyN
    simpa only [F,φ,inner_zero_left] using hz.inner hep.2
  have hproduct : Tendsto (fun n => bochnerL2ProductIsometry (V n)) atTop
      (𝓝 (finiteTensorTestMultiplier T η ψ hη).toL2) := by
    rw [← finiteTensorTestMultiplier_eq_product T htpos η f ψ hη hf hd]
    exact bochnerL2ProductIsometry.continuous.tendsto _ |>.comp hV
  have hP : Tendsto (fun n => inner ℝ (P n) (V n)) atTop
      (𝓝 (inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (finiteTensorTestMultiplier T η ψ hη).toL2)) :=
    time_average_reconstructed_weak_pairing T htpos.le g hT htlim b (finiteTensorTestMultiplier T η ψ hη)
      (fun n i => (y n i.succ : Lp ℝ 2 (volume.restrict S)))
      (fun n i => (φ n i.castSucc : Lp ℝ 2 (volume.restrict S))) Yv hE hwE hproduct
  have hleft := ((hilbert_weak_strong_pairing E D Yv Φd hE hwE hD).neg.add
    (hilbert_weak_strong_pairing G H Yg Φg hG hwG hH)).add hP
  have hright := (hI.add (hilbert_weak_strong_pairing K V U Φ hK hwK hV)).sub hF
  have heq : (fun n => -inner ℝ (E n) (D n)+inner ℝ (G n) (H n)+inner ℝ (P n) (V n))=
      (fun n => I n+inner ℝ (K n) (V n)-F n) := by
    funext n
    exact conforming_fixed_forward_reconstructed_weak_identity hS hdim hSb
      ((mesh n).conformingSpace (dirichletSubspace S)) ((mesh n).conformingSpace_le (dirichletSubspace S))
      T ω (g n) (hT n) (fixedTimeCellPotential T (g n) (hT n) b) (u n) (y n) (φ n) (hy n)
  rw [heq] at hleft
  simpa only [sub_zero] using tendsto_nhds_unique hleft hright

end Carleman
