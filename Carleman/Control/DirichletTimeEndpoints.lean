module

public import Carleman.Control.ScalarTimeEndpoints
public import Carleman.Control.DirichletTimeContinuity

/-! The unrestricted original weak control identity fixes the continuous initial and terminal states. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.continuous_pairing_weak
    {T : ℝ} (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (g : TimeGrid) (hT : g.period=T)
    (q : ℝ → Lp ℝ 2 (volume.restrict S))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)))
    (w : DirichletEnergyState S) :
    HasWeakTimeDerivative g (fun t => inner ℝ (q t) (dirichletStateValue S w))
      (fun t => inner ℝ (dirichletTimeLoad T hS b Y U t) w) := by
  let := dirichletEnergyState_complete hS
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  let mY := (dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y
  let D := dirichletTimeLoad T hS b Y U
  have hm : MemLp mY 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp mY
  have hd : MemLp D 2 g.timeMeasure := by rw [hμ]; exact Lp.memLp D
  have hwm : HasWeakTimeDerivative g (fun t => inner ℝ w (mY t)) (fun t => inner ℝ w (D t)) := by
    intro φ hs hc hsup
    exact (hid.mass_weak_time_derivative hS g hT).map_integral hm hd (innerSL ℝ w) φ hs hc hsup
  have he : (fun t => inner ℝ w (mY t)) =ᵐ[g.timeMeasure]
      (fun t => inner ℝ (q t) (dirichletStateValue S w)) := by
    rw [hμ]
    filter_upwards [(dirichletTimeMass S hS).coeFn_compLpL Y,hq] with t ht hqt
    change mY t=dirichletTimeMass S hS (Y t) at ht
    rw [ht,hqt]
    change inner ℝ w ((dirichletStateValue S).adjoint (dirichletStateValue S (Y t)))=
      inner ℝ (dirichletStateValue S (Y t)) (dirichletStateValue S w)
    rw [ContinuousLinearMap.adjoint_inner_right,real_inner_comm]
  have hh := hwm.congr_value he
  simpa only [real_inner_comm] using hh

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.continuous_pairing_test
    {T : ℝ} (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (q : ℝ → Lp ℝ 2 (volume.restrict S))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)))
    (η f : ℝ → ℝ) (hη : ContinuousOn η (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t, t ∈ Icc 0 T → HasDerivWithinAt η (f t) (Icc 0 T) t)
    (w : DirichletEnergyState S) :
    -(∫ t, f t*inner ℝ (q t) (dirichletStateValue S w) ∂(volume.restrict (Ioc 0 T)))=
      η 0*inner ℝ y0 (dirichletStateValue S w)+
        (∫ t, η t*inner ℝ (dirichletTimeLoad T hS b Y U t) w ∂(volume.restrict (Ioc 0 T))) := by
  let := dirichletEnergyState_complete hS
  have ht := hid.mass_test_identity hTpos hS η f hη hf hd w
  rw [timeTensor_eq_scalarTensor,timeTensor_eq_scalarTensor,inner_scalarTensor,inner_scalarTensor,
    real_inner_smul_right] at ht
  have he₁ : (∫ t, ((continuous_time_memLp T f hf).toLp f) t*
      inner ℝ (((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y) t) w
        ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, f t*inner ℝ (q t) (dirichletStateValue S w) ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [(continuous_time_memLp T f hf).coeFn_toLp,
      (dirichletTimeMass S hS).coeFn_compLpL Y,hq] with t hf ht hqt
    rw [hf,ht,hqt]
    congr 1
    exact (dirichletStateValue S).adjoint_inner_left w (dirichletStateValue S (Y t))
  have he₂ : (∫ t, ((continuous_time_memLp T η hη).toLp η) t*
      inner ℝ (dirichletTimeLoad T hS b Y U t) w ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, η t*inner ℝ (dirichletTimeLoad T hS b Y U t) w ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [(continuous_time_memLp T η hη).coeFn_toLp] with t ht
    rw [ht]
  rwa [he₁,he₂] at ht

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.continuous_H_endpoints
    {T : ℝ} (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (q : ℝ → Lp ℝ 2 (volume.restrict S)) (hc : ContinuousOn q (Icc 0 T))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t))) :
    q 0=y0 ∧ q T=0 := by
  let := dirichletEnergyState_complete hS
  let g : TimeGrid := ⟨1,by decide,T,hTpos⟩
  have hT : g.period=T := by simp [g,TimeGrid.period]
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  let D := dirichletTimeLoad T hS b Y U
  have hpair (w : DirichletEnergyState S) :
      inner ℝ (q 0) (dirichletStateValue S w)=inner ℝ y0 (dirichletStateValue S w) ∧
        inner ℝ (q T) (dirichletStateValue S w)=0 := by
    have hw := hid.continuous_pairing_weak hS g hT q hq w
    have hfc : ContinuousOn (fun t => inner ℝ (q t) (dirichletStateValue S w)) (Icc 0 g.period) := by
      rw [hT]
      exact hc.inner (𝕜 := ℝ) continuousOn_const
    have hfd : MemLp (fun t => inner ℝ (D t) w) 2 g.timeMeasure := by
      rw [hμ]
      simpa only [innerSL_apply_apply,real_inner_comm] using (Lp.memLp D).continuousLinearMap_comp (innerSL ℝ w)
    have hz := hid.continuous_pairing_test hTpos hS q hq (fun _ => 1) (fun _ => 0)
      continuousOn_const continuousOn_const (fun t _ => (hasDerivAt_const t (1:ℝ)).hasDerivWithinAt) w
    have hl := hid.continuous_pairing_test hTpos hS q hq id (fun _ => 1)
      continuousOn_id continuousOn_const (fun t _ => (hasDerivAt_id t).hasDerivWithinAt) w
    simp only [zero_mul,integral_zero,neg_zero,one_mul] at hz
    simp only [id_eq,one_mul,zero_mul,zero_add] at hl
    have he := hw.scalar_endpoints hfc hfd (inner ℝ y0 (dirichletStateValue S w))
      (by rw [hμ]; exact hz.symm) (by rw [hμ]; linarith [hl])
    simpa only [hT] using he
  have hdense : DenseRange (dirichletStateValue S) :=
    conformingEmbed_dense (dirichletSubspace S) (dirichletSubspace_sobolev S) (dirichletSubspace_dense S hS)
  constructor
  · apply ext_inner_right ℝ
    intro z
    exact hdense.induction_on z (isClosed_eq (continuous_const.inner (𝕜 := ℝ) continuous_id)
      (continuous_const.inner (𝕜 := ℝ) continuous_id)) (fun w => (hpair w).1)
  · apply ext_inner_right ℝ
    intro z
    rw [inner_zero_left]
    exact hdense.induction_on z (isClosed_eq (continuous_const.inner (𝕜 := ℝ) continuous_id) continuous_const)
      (fun w => (hpair w).2)

theorem FiniteDirichletControlIdentity.continuous_H_trace
    {T : ℝ} (hTpos : 0 < T) (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U) :
    ∃ q : ℝ → Lp ℝ 2 (volume.restrict S), ContinuousOn q (Icc 0 T) ∧
      q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)) ∧
      q 0=y0 ∧ q T=0 := by
  obtain ⟨q,hc,hq⟩ := hid.continuous_H_representative hTpos hS
  exact ⟨q,hc,hq,hid.continuous_H_endpoints hTpos hS q hc hq⟩

end Carleman
