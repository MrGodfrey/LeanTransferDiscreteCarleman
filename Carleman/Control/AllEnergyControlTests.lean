module

public import Carleman.Control.FiniteWeakControlIdentity
public import Carleman.Control.FiniteTensorProductIdentity
public import Carleman.Control.DirichletTestDensity

/-! The original control weak equation extends to every Dirichlet energy test. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman
variable {d : ℕ}

attribute [local irreducible] timeTensor bochnerL2ProductIsometry

set_option maxHeartbeats 1200000 in
theorem FiniteDirichletControlIdentity.spatial_test
    {T : ℝ} (hTpos : 0 < T) {S : Set (SpatialCoordinates d)} 
    [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (η f : ℝ → ℝ) (hη : ContinuousOn η (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t, t ∈ Icc 0 T → HasDerivWithinAt η (f t) (Icc 0 T) t)
    (ψ : SpatialTest S) :
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let ηLp := (continuous_time_memLp T η hη).toLp η;
    let fLp := (continuous_time_memLp T f hf).toLp f;
    -inner ℝ Yv (timeTensor T (dirichletStateValue S ψ.dirichletState) fLp)+
      inner ℝ Yg (timeTensor T (dirichletStateGradient S ψ.dirichletState) ηLp)+
      inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (bochnerL2ProductIsometry (timeTensor T (dirichletStateValue S ψ.dirichletState) ηLp))=
      inner ℝ y0 (η 0 • dirichletStateValue S ψ.dirichletState)+inner ℝ U (timeTensor T (dirichletStateValue S ψ.dirichletState) ηLp) := by
  intro Yv Yg ηLp fLp
  have ht := hid 1 (fun _ => η) (fun _ => f) (fun _ => ψ) (fun _ => hη) (fun _ => hf) (fun _ => hd)
  have hp := finiteTensorTestMultiplier_eq_product T hTpos (L := Fin 1)
    (fun _ => η) (fun _ => f) (fun _ => ψ) (fun _ => hη) (fun _ => hf) (fun _ => hd)
  dsimp only at ht
  rw [← hp] at ht
  simpa only [Fin.sum_univ_one,SpatialTest.dirichletState_value] using ht

set_option maxHeartbeats 1200000 in
theorem FiniteDirichletControlIdentity.all_energy_tests
    {T : ℝ} (hTpos : 0 < T) {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (η f : ℝ → ℝ) (hη : ContinuousOn η (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t, t ∈ Icc 0 T → HasDerivWithinAt η (f t) (Icc 0 T) t)
    (w : DirichletEnergyState S) :
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let ηLp := (continuous_time_memLp T η hη).toLp η;
    let fLp := (continuous_time_memLp T f hf).toLp f;
    -inner ℝ Yv (timeTensor T (dirichletStateValue S w) fLp)+
      inner ℝ Yg (timeTensor T (dirichletStateGradient S w) ηLp)+
      inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (bochnerL2ProductIsometry (timeTensor T (dirichletStateValue S w) ηLp))=
      inner ℝ y0 (η 0 • dirichletStateValue S w)+inner ℝ U (timeTensor T (dirichletStateValue S w) ηLp) := by
  intro Yv Yg ηLp fLp
  have htest := fun ψ : SpatialTest S => hid.spatial_test hTpos η f hη hf hd ψ
  have hdense := exists_dirichlet_test_sequence (d := d) (S := S) hS w
  obtain ⟨ψ,hψ⟩ := hdense
  have hvη : Continuous (fun w : DirichletEnergyState S => timeTensor T (dirichletStateValue S w) ηLp) :=
    ((timeTensor (H := Lp ℝ 2 (volume.restrict S)) T).flip ηLp).continuous.comp (dirichletStateValue S).continuous
  have hvf : Continuous (fun w : DirichletEnergyState S => timeTensor T (dirichletStateValue S w) fLp) :=
    ((timeTensor (H := Lp ℝ 2 (volume.restrict S)) T).flip fLp).continuous.comp (dirichletStateValue S).continuous
  have hgη : Continuous (fun w : DirichletEnergyState S => timeTensor T (dirichletStateGradient S w) ηLp) :=
    ((timeTensor (H := Lp (DerivativeFiber d 1) 2 (volume.restrict S)) T).flip ηLp).continuous.comp (dirichletStateGradient S).continuous
  have hp := bochnerL2ProductIsometry.continuous.comp hvη
  have hl := (((continuous_const (y := Yv)).inner (𝕜 := ℝ) hvf).neg.add
    ((continuous_const (y := Yg)).inner (𝕜 := ℝ) hgη)).add
    ((continuous_const (y := b.map (bochnerL2ProductIsometry Yv))).inner (𝕜 := ℝ) hp)
  have hr := ((continuous_const (y := y0)).inner (𝕜 := ℝ) ((dirichletStateValue S).continuous.const_smul (η 0))).add
    ((continuous_const (y := U)).inner (𝕜 := ℝ) hvη)
  exact (isClosed_eq hl hr).mem_of_tendsto hψ (Eventually.of_forall (fun n => htest (ψ n)))

end Carleman
