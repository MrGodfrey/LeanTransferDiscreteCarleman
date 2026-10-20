module
public import Carleman.Control.FullP1NumericalData
public import Carleman.Spatial.FiniteHalfspaceRegularity
/-! Original Proposition 6.1 on every bounded convex polytope. The actual
Dirichlet domain regularity is supplied internally, using the proved original
projected weighted test and its actual derivative. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable

theorem finite_halfspace_convex {d : ℕ} {ι : Type*}
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ {x | ∀ i, b i < ℓ i x} := by
  have he : {x | ∀ i, b i < ℓ i x} = ⋂ i, {x | b i < ℓ i x} := by ext x; simp
  rw [he]
  exact convex_iInter fun i => convex_halfSpace_gt ⟨(ℓ i).map_add, (ℓ i).map_smul⟩ (b i)

theorem finite_halfspace_p1_realization {d : ℕ} {κidx : Type*} [Fintype κidx]
    (hdpos : 0 < d) (hdim : d ≤ 3)
    (L : κidx → SpatialCoordinates d →L[ℝ] ℝ) (b : κidx → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i < L i x})
    {z : SpatialCoordinates d} (hz : ∀ i, b i < L i z)
    (ρ : SpatialProfile (volume.restrict {x | ∀ i, b i < L i x}))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure {x | ∀ i, b i < L i x}))
    (κ c B γ β τStar : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀) (hinc : ω₀ ⊆ ω) :
    let S := {x | ∀ i, b i < L i x}
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
    let a := boundedDirichletOriginalForm (finite_halfspace_isOpen L b) hdpos hb
    let hD := finite_halfspace_dirichlet_domain_le_h2 hdpos L b hb hz
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
      ∃ (Capp : ℝ) (hCa : 0 < Capp),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
      M.FaceMatching → M.BoundaryFitted →
    ∀ (centers : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (centers i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight) (g : TimeGrid) (_H : TimeWeightRegularity w g β), M.maxDiameter*w.max ≤ δ →
    let X := M.conformingSpace (dirichletSubspace S)
    let hX := M.conformingSpace_le (dirichletSubspace S)
    Nonempty (Section5.NumericalData a hD (Physical.conformingReconstruction (dirichletSubspace S) X hX)
      (Physical.galerkinStiffness a X hX).toLinearMap 0 (Physical.conformingLoad (dirichletSubspace S) X hX)
      (Physical.conformingRegionControl X ω).adjoint.toLinearMap g w ρ ω₀ hω₀
      (Physical.conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => ((ρ.multiplier w 0 t).restrictMeasure Measure.restrict_le_self).seminorm)
      τStar Ctime Csuper 1 M.maxDiameter (p1ErrorScales Capp M.maxDiameter hCa.le M.maxDiameter_nonneg)) := by
  let S := {x | ∀ i, b i < L i x}
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  dsimp only
  obtain ⟨δ,hδ,hδ1,Ctime,hCt,Csuper,hCs,Capp,hCa,hnum⟩ :=
    full_p1_numericalData hdpos hdim (finite_halfspace_isOpen L b)
      (finite_halfspace_convex L b) hb.isCompact_closure ρ hρ κ c B γ β τStar
      hκ hcpos hBpos hγ hΓ hβ hτStar ω₀ ω hω₀ hinc
  refine ⟨δ,hδ,hδ1,Ctime,hCt,Csuper,hCs,Capp,hCa,?_⟩
  intro ι _ M hM hBnd centers r ℓ hr hball hshape hℓ hlow hupp hg w g H hm
  exact hnum ι M hM hBnd centers r ℓ hr hball hshape hℓ hlow hupp hg
    (finite_halfspace_dirichlet_domain_le_h2 hdpos L b hb hz) w g H hm

end Carleman
