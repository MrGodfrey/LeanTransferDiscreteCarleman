module

public import Carleman.Control.BoxP1PhysicalControl
public import Carleman.Control.FilterPenaltyBound

/-! Terminal-filtered observability and actual regional filtered controls for the full P1 spaces. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_p1_filtered_observation_control (hdim : d+1 ≤ 3)
    (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {ω : Set (SpatialCoordinates (d+1))} (hω : IsOpen ω) (hne : ω.Nonempty)
    (hωS : ω ⊆ openCoordinateBox lo hi)
    (shape cmesh Bmesh γ : ℝ) (hshape : 0 < shape) (hcmesh : 0 < cmesh) (hBmesh : 0 < Bmesh)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit (d+1)) :
    let S := openCoordinateBox lo hi
    let a := boundedDirichletOriginalForm (openCoordinateBox_isOpen lo hi) (Nat.zero_lt_succ d)
      (openCoordinateBox_isBounded lo hi)
    ∃ qc κ h0 Δ0 Cb d0 : ℝ, 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cb ∧ 0 < d0 ∧
      ∀ (T Mbound : ℝ), 0 < T → 0 ≤ Mbound → ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
      let X := M.conformingSpace (dirichletSubspace S)
      let hX : X ≤ a.V := M.conformingSpace_le (dirichletSubspace S)
      M.FaceMatching → M.BoundaryFitted →
      ∀ (centers : ι → SpatialCoordinates (d+1)) (r ℓ : ι → ℝ),
        (∀ i, 0 < r i) → (∀ i, Metric.ball (centers i) (r i) ⊆ M.cell i) →
        (∀ i, M.cellDiameter i ≤ shape*r i) → (∀ i, 0 < ℓ i) →
        (∀ i, cmesh*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ Bmesh*M.cellDiameter i) →
        (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
        M.maxDiameter ≤ h0 →
      ∀ g : TimeGrid, g.period = T → g.dt ≤ Δ0 →
        let Smax := physicalMeshScale κ M.maxDiameter g.dt
        16*physicalBaseAmplitude Cb qc T Mbound ≤ Smax →
        Smax ≤ physicalBaseAmplitude Cb qc T Mbound*T/(4*g.dt) →
        g.dt*Mbound ≤ 1/2 → g.dt ≤ T/12 →
      ∀ (b : Fin g.steps → BoundedMultiplier (volume.restrict S)), (∀ i, (b i).bound ≤ Mbound) →
      ∀ (θ : ℝ) (F : Submodule ℝ ↥(M.conformingSpace (dirichletSubspace S))),
        T*filterRayleigh (galerkinStiffness a X hX) F ≤ θ*d0*Smax →
        Mbound*T+Mbound^2*T^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d0*Smax →
        PhysicalFilteredObservationControl g (fun i => galerkinStiffness a X hX+conformingPotential X (b i))
          (conformingRegionControl X ω) C0 θ d0 Smax F := by
  let S := openCoordinateBox lo hi
  dsimp only
  obtain ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,hobs⟩ :=
    box_p1_physical_observation_control hdim lo hi hpos hω hne hωS shape cmesh Bmesh γ
      hshape hcmesh hBmesh hγ hΓ
  refine ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T Mbound hT hMb
  obtain ⟨C,_hC,hdata⟩ := hobs T Mbound hT hMb
  let C0 := max 1 (max C (2*(filterTerminalFactor T Mbound)^2))
  have hC0 : 1 ≤ C0 := le_max_left _ _
  have hCC0 : C ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hbudget : 2*(filterTerminalFactor T Mbound)^2 ≤ C0 :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C0,hC0,?_⟩
  intro ι _ M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hmesh g hgT hdt hS hmeshS hsmall hdtT
  let Smax := physicalMeshScale κ M.maxDiameter g.dt
  intro b hb θ F hΛ hgap
  let a := boundedDirichletOriginalForm (openCoordinateBox_isOpen lo hi) (Nat.zero_lt_succ d)
    (openCoordinateBox_isBounded lo hi)
  let X := M.conformingSpace (dirichletSubspace S)
  let hX : X ≤ a.V := M.conformingSpace_le (dirichletSubspace S)
  have hrelax := (hdata ι M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hmesh
    g hgT hdt hS hmeshS hsmall hdtT b hb).1
  have ho (z : Fin (g.steps+1) → X)
      (hz : AdjointEquation g.dt (fun i => galerkinStiffness a X hX+conformingPotential X (b i)) z) :
      ‖z 0‖^2 ≤ C0*((g.dt*∑ i : Fin g.steps,
        ‖(conformingRegionControl X ω).adjoint (z i.castSucc)‖^2)+
        Real.exp (-2*d0*Smax)*‖z (Fin.last g.steps)‖^2) := by
    apply (hrelax z hz).trans
    apply mul_le_mul_of_nonneg_right hCC0
    exact add_nonneg (mul_nonneg g.dt_pos.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hΛg : g.period*filterRayleigh (galerkinStiffness a X hX) F ≤ θ*d0*Smax := by
    simpa only [hgT] using hΛ
  have hgapg : Mbound*g.period+Mbound^2*g.period^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d0*Smax := by
    simpa only [hgT] using hgap
  refine ⟨?_,?_⟩
  · exact filtered_observation_of_relaxed g Mbound θ d0 Smax C0 hMb hsmall hC0
      (galerkinStiffness a X hX) (galerkinStiffness_symmetric a X hX) (galerkinStiffness_nonneg a X hX)
      (fun i => conformingPotential X (b i)) (fun i => conformingPotential_symmetric X (b i))
      (fun i => (conformingPotential_norm X (b i)).trans (hb i)) (conformingRegionControl X ω)
      ho F hΛg hgapg
  · intro y0
    obtain ⟨u,y,hy0,hy,hu,hproj,hterm⟩ := filtered_control_of_relaxed g Mbound θ d0 Smax C0
      hMb hsmall hC0 (galerkinStiffness a X hX) (galerkinStiffness_symmetric a X hX)
      (galerkinStiffness_nonneg a X hX) (fun i => conformingPotential X (b i))
      (fun i => conformingPotential_symmetric X (b i))
      (fun i => (conformingPotential_norm X (b i)).trans (hb i)) (conformingRegionControl X ω)
      ho F hΛg hgapg y0
    refine ⟨u,y,hy0,hy,hu,hproj,?_⟩
    rw [hgT] at hterm
    have hpen := filter_penalty_decay T Mbound (filterRayleigh (galerkinStiffness a X hX) F)
      θ d0 Smax hT.le hMb (filterRayleigh_nonneg _ (galerkinStiffness_nonneg a X hX) F) hΛ
    have h1 := mul_le_mul_of_nonneg_right hpen
      (mul_nonneg (Real.sqrt_nonneg (2*C0)) (norm_nonneg y0))
    have h2 := mul_le_mul_of_nonneg_right
      (filter_terminal_constant_budget T Mbound C0 (zero_le_one.trans hC0) hbudget)
      (mul_nonneg (Real.exp_pos (-(1-θ)*d0*Smax)).le (norm_nonneg y0))
    change Real.sqrt (2*C0)*(Real.sqrt (1+2*(Real.exp (2*Mbound*T))^2)*Real.exp (Mbound*T+Mbound^2*T^2/2))*
      (Real.exp (-(1-θ)*d0*Smax)*‖y0‖) ≤ _ at h2
    nlinarith only [hterm,h1,h2]

end Carleman.Physical
