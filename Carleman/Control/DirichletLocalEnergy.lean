module

public import Carleman.Control.DirichletTimeEnergyIdentity
public import Carleman.Control.BochnerProductCutoff

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Carleman
variable {α β V H : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure α} {ν : Measure β}

set_option backward.isDefEq.respectTransparency true in
theorem dirichletTimeLoad_cutoff_pairing
    {d : ℕ} {S : Set (SpatialCoordinates d)} (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (s : Set ℝ) (hs : MeasurableSet s) :
    let W := BoundedMultiplier.cutoff (ν := volume.restrict (Ioc 0 T)) s hs;
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    inner ℝ (dirichletTimeLoad T hS b Y U) (W.map Y)=
      inner ℝ (W.map U) (W.map Yv)-‖W.map Yg‖^2-
      inner ℝ (b.map (bochnerL2ProductIsometry (W.map Yv)))
        (bochnerL2ProductIsometry (W.map Yv)) := by
  let := dirichletEnergyState_complete hS
  intro W Yv Yg
  dsimp only [dirichletTimeLoad]
  simp only [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,
    BoundedMultiplier.compLpL_map,LinearIsometry.coe_toContinuousLinearMap]
  change inner ℝ U (W.map Yv)-inner ℝ Yg (W.map Yg)-
      inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (bochnerL2ProductIsometry (W.map Yv))=_
  have hcontrol := cutoff_inner_cutoff s hs U Yv
  have hgrad := cutoff_inner_cutoff s hs Yg Yg
  rw [real_inner_self_eq_norm_sq] at hgrad
  rw [hcontrol,hgrad]
  congr 1
  rw [bochnerL2ProductIsometry_cutoff,cutoff_multiplier_pairing]

set_option backward.isDefEq.respectTransparency true in
theorem dirichletTimeLoad_cutoff_upper_bound
    {d : ℕ} {S : Set (SpatialCoordinates d)} (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (s : Set ℝ) (hs : MeasurableSet s) :
    let W := BoundedMultiplier.cutoff (ν := volume.restrict (Ioc 0 T)) s hs;
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    inner ℝ (dirichletTimeLoad T hS b Y U) (W.map Y)+‖W.map Yg‖^2 ≤
      ‖W.map U‖*‖W.map Yv‖+b.bound*‖W.map Yv‖^2 := by
  intro W Yv Yg
  rw [dirichletTimeLoad_cutoff_pairing]
  let z := bochnerL2ProductIsometry (W.map Yv)
  have hp : |inner ℝ (b.map z) z| ≤ b.bound*‖W.map Yv‖^2 := by
    have h := (abs_real_inner_le_norm (b.map z) z).trans
      (mul_le_mul_of_nonneg_right (b.seminorm_le z) (norm_nonneg z))
    simpa only [z,LinearIsometry.norm_map,mul_assoc,pow_two] using h
  have hc := real_inner_le_norm (W.map U) (W.map Yv)
  have hneg := neg_le_abs (inner ℝ (b.map z) z)
  dsimp only [W,Yv,Yg] at hp hc hneg ⊢
  nlinarith

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.local_energy_inequality
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (q : ℝ → Lp ℝ 2 (volume.restrict S)) (hc : ContinuousOn q (Icc 0 T))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    let W := BoundedMultiplier.cutoff (ν := volume.restrict (Ioc 0 T)) (Ioc 0 t) measurableSet_Ioc;
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    ‖q t‖^2-‖q 0‖^2+2*‖W.map Yg‖^2 ≤
      2*(‖W.map U‖*‖W.map Yv‖+b.bound*‖W.map Yv‖^2) := by
  intro W Yv Yg
  have he := hid.energy_identity hTpos hS q hc hq t ht
  have hi : inner ℝ (dirichletTimeLoad T hS b Y U) (W.map Y)=
      ∫ s in 0..t, inner ℝ (Y s) (dirichletTimeLoad T hS b Y U s) := by
    rw [cutoff_inner_integral,intervalIntegral.integral_of_le ht.1]
    have hμ : (volume.restrict (Ioc 0 T)).restrict (Ioc 0 t)=volume.restrict (Ioc 0 t) := by
      rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)]
    rw [hμ]
    exact integral_congr_ae (Eventually.of_forall fun _ => real_inner_comm _ _)
  have hb := dirichletTimeLoad_cutoff_upper_bound T hS b Y U (Ioc 0 t) measurableSet_Ioc
  change inner ℝ (dirichletTimeLoad T hS b Y U) (W.map Y)+‖W.map Yg‖^2 ≤
    ‖W.map U‖*‖W.map Yv‖+b.bound*‖W.map Yv‖^2 at hb
  rw [← hi] at he
  linarith


end Carleman
