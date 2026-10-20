module

public import Carleman.Control.DirichletTimeLoad
public import Carleman.Control.AllEnergyControlTests

/-! The original weak identity gives the actual energy-valued derivative of the pivot mass. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal ContDiff
namespace Carleman

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem FiniteDirichletControlIdentity.mass_test_identity
    {T : ℝ} (hTpos : 0 < T) (hS : IsOpen S)
    [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (η f : ℝ → ℝ) (hη : ContinuousOn η (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t, t ∈ Icc 0 T → HasDerivWithinAt η (f t) (Icc 0 T) t)
    (w : DirichletEnergyState S) :
    -inner ℝ ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (timeTensor T w ((continuous_time_memLp T f hf).toLp f))=
    inner ℝ y0 (η 0 • dirichletStateValue S w)+
      inner ℝ (dirichletTimeLoad T hS b Y U) (timeTensor T w ((continuous_time_memLp T η hη).toLp η)) := by
  have ht := hid.all_energy_tests hTpos hS η f hη hf hd w
  dsimp only at ht
  rw [dirichletTimeMass_pairing,dirichletTimeLoad_pairing]
  linarith

theorem FiniteDirichletControlIdentity.mass_weak_time_derivative
    {T : ℝ} (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (g : TimeGrid) (hT : g.period=T) :
    HasWeakTimeDerivative g
      ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (dirichletTimeLoad T hS b Y U) := by
  let := dirichletEnergyState_complete hS
  intro φ hφ hc hs
  have hTpos : 0 < T := hT ▸ g.period_pos
  have hη : ContinuousOn φ (Icc 0 T) := hφ.continuous.continuousOn
  have hf : ContinuousOn (deriv φ) (Icc 0 T) := (hφ.continuous_deriv (by simp)).continuousOn
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt φ (deriv φ t) (Icc 0 T) t :=
    (hφ.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hzero : φ 0=0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl 0) (hs h).1)
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  rw [hμ]
  apply ext_inner_right ℝ
  intro w
  rw [inner_neg_left]
  have ht := hid.mass_test_identity hTpos hS φ (deriv φ) hη hf hd w
  simp only [hzero,zero_smul,inner_zero_right,zero_add] at ht
  rw [inner_timeTensor_integral,inner_timeTensor_integral] at ht
  have he₁ : (∫ t, ((continuous_time_memLp T (deriv φ) hf).toLp (deriv φ)) t •
      ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y) t ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, deriv φ t • ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y) t ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [(continuous_time_memLp T (deriv φ) hf).coeFn_toLp] with t ht
    rw [ht]
  have he₂ : (∫ t, ((continuous_time_memLp T φ hη).toLp φ) t • (dirichletTimeLoad T hS b Y U) t ∂(volume.restrict (Ioc 0 T)))=
      ∫ t, φ t • (dirichletTimeLoad T hS b Y U) t ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_congr_ae
    filter_upwards [(continuous_time_memLp T φ hη).coeFn_toLp] with t ht
    rw [ht]
  rw [he₁,he₂] at ht
  linarith


end Carleman
