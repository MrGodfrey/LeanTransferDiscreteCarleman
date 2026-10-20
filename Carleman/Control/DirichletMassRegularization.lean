module

public import Carleman.Control.MassRegularizerStrong
public import Carleman.Control.DirichletTimeLoad

/-! The true Dirichlet pivot mass has contractive regularizers converging in the full energy and Bochner norms. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem dirichletTimeMass_nonneg (hS : IsOpen S) (v : DirichletEnergyState S) :
    0 ≤ inner ℝ (dirichletTimeMass S hS v) v := by
  let := dirichletEnergyState_complete hS
  change 0 ≤ inner ℝ ((dirichletStateValue S).adjoint (dirichletStateValue S v)) v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact real_inner_self_nonneg

theorem dirichletTimeMass_dense (hS : IsOpen S) : DenseRange (dirichletTimeMass S hS) := by
  let := dirichletEnergyState_complete hS
  apply adjoint_mass_denseRange (dirichletStateValue S)
  exact conformingEmbed_injective (dirichletSubspace S) hS (ae_restrict_mem hS.measurableSet)

def dirichletMassRegularizer (S : Set (SpatialCoordinates d)) (hS : IsOpen S)
    (ε : ℝ) (hε : 0 < ε) : DirichletEnergyState S →L[ℝ] DirichletEnergyState S := by
  letI := dirichletEnergyState_complete hS
  exact positiveMassRegularizer (dirichletTimeMass S hS) (dirichletTimeMass_nonneg hS) ε hε

theorem dirichletMassRegularizer_norm (hS : IsOpen S) (ε : ℝ) (hε : 0 < ε)
    (v : DirichletEnergyState S) : ‖dirichletMassRegularizer S hS ε hε v‖ ≤ ‖v‖ := by
  let := dirichletEnergyState_complete hS
  exact positiveMassRegularizer_norm (dirichletTimeMass S hS) (dirichletTimeMass_nonneg hS) ε hε v

theorem dirichletMassRegularizer_strong (hS : IsOpen S) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (v : DirichletEnergyState S) :
    Tendsto (fun n => dirichletMassRegularizer S hS (ε n) (hε n) v) atTop (𝓝 v) := by
  let := dirichletEnergyState_complete hS
  exact positiveMassRegularizer_strong (dirichletTimeMass S hS) (dirichletTimeMass_nonneg hS)
    (dirichletTimeMass_dense hS) ε hε hlim v


theorem dirichletMassRegularizer_bochner_strong (hS : IsOpen S) (T : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))) :
    Tendsto (fun n => (dirichletMassRegularizer S hS (ε n) (hε n)).compLpL 2
      (volume.restrict (Ioc 0 T)) Y) atTop (𝓝 Y) := by
  let := dirichletEnergyState_complete hS
  exact compLpL_strong_of_contractions (volume.restrict (Ioc 0 T))
    (fun n => dirichletMassRegularizer S hS (ε n) (hε n))
    (fun n => dirichletMassRegularizer_norm hS (ε n) (hε n))
    (dirichletMassRegularizer_strong hS ε hε hlim) Y

end Carleman
