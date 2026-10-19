module

public import Carleman.Control.BoxP1LoadCarleman
public import Carleman.Control.PhysicalIntervalQClass
public import Carleman.Control.PhysicalControlConclusion

/-! Original physical observability and actual regional controls for all admissible full P1 meshes. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_p1_physical_observation_control (hdim : d+1 ≤ 3)
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
      ∀ (T Mbound : ℝ), 0 < T → 0 ≤ Mbound → ∃ Cphys : ℝ, 0 < Cphys ∧
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
        PhysicalObservationControl g (fun i => galerkinStiffness a X hX+conformingPotential X (b i))
          (conformingRegionControl X ω) Cphys d0 Smax := by
  let S := openCoordinateBox lo hi
  dsimp only
  obtain ⟨c,l,β,qc,κ,h0,Δ0,CCE,_hc,hl,hβ,_hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCCE,hload⟩ :=
    box_p1_physical_load_carleman hdim lo hi hpos hω hne hωS shape cmesh Bmesh γ
      hshape hcmesh hBmesh hγ hΓ
  let ρ := interiorSpatialProfile (volume.restrict S) c (zero_le_one.trans hl)
  have hneg : ∀ᵐ x ∂volume.restrict S, ρ.value x ≤ -(1:ℝ) :=
    Filter.Eventually.of_forall fun x => (interiorCarlemanProfile_bounds c (zero_le_one.trans hl) x).2
  obtain ⟨Cb,d0,hCb,hd0,hobs⟩ := conforming_observation_control_uniform (E := ℝ) ρ ω hω.measurableSet
    β qc CCE 1 hβ hqc hCCE.le zero_lt_one hneg
  refine ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T Mbound hT hMb
  obtain ⟨Cphys,hCp,hdata⟩ := hobs T Mbound hT hMb
  refine ⟨Cphys,hCp,?_⟩
  intro ι _ M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hmesh g hgT hdt hS hmeshS hsmall hdtT
  let Smax := physicalMeshScale κ M.maxDiameter g.dt
  intro b hb
  let a := boundedDirichletOriginalForm (openCoordinateBox_isOpen lo hi) (Nat.zero_lt_succ d)
    (openCoordinateBox_isBounded lo hi)
  let X := M.conformingSpace (dirichletSubspace S)
  let hX : X ≤ a.V := M.conformingSpace_le (dirichletSubspace S)
  exact hdata X g hgT Smax hS hmeshS hsmall hdtT (galerkinStiffness a X hX)
    (galerkinStiffness_symmetric a X hX) (galerkinStiffness_nonneg a X hX) b hb
    (fun w hw hmax => hload ι M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hmesh
      g w hw.toInterval hdt hmax)

end Carleman.Physical
