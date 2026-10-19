module

public import Carleman.Control.FullP1Superapproximation

/-! The full original P1 space supplies the complete actual WeightedTest,
with a single set of constants before all graded meshes and time weights. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem full_p1_weightedTest_interface
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ c B γ β τStar : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using (hcompact.isBounded.subset subset_closure).measure_lt_top (μ := volume)⟩
    ∃ ε > (0:ℝ), ε ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
    ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ ε →
    ∀ (g : TimeGrid) (H : TimeWeightRegularity w g β) (τ η : ℝ), |τ| ≤ τStar → |η|=1 →
    let X := M.conformingSpace (dirichletSubspace S)
    ∃ T : Section4.WeightedTest hS (ae_restrict_mem hS.measurableSet)
      (dirichletSubspace_sobolev S)
      (Physical.conformingReconstruction (dirichletSubspace S) X
        (M.conformingSpace_le (dirichletSubspace S))) g (ρ.scaled η) w τ Ctime Csuper M.maxDiameter,
      T.op=(fun t => (Physical.galerkinWeightedTest X (ρ.scaled η) w τ t).toLinearMap) ∧
      T.derivative=(fun t => (Physical.galerkinWeightedTestDerivative X (ρ.scaled η) w H τ t).toLinearMap) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using (hcompact.isBounded.subset subset_closure).measure_lt_top (μ := volume)⟩
  obtain ⟨ε,hε,he1,Csuper,hCs,hsuper⟩ := full_p1_galerkin_superapproximation
    hS hc hcompact ρ hρ κ c B γ hκ hcpos hBpos hγ hΓ
  let Ctime := 2*β*(τStar+ρ.bound)+1
  have hCt : 0 < Ctime := by dsimp only [Ctime]; positivity [ρ.bound_nonneg]
  refine ⟨ε,hε,he1,Ctime,hCt,Csuper,hCs,?_⟩
  intro ι _ M hM hB a r ℓ hr hball hshape hℓ hlow hupp hg w hm g H τ η hτ hη
  let X := M.conformingSpace (dirichletSubspace S)
  let hX := M.conformingSpace_le (dirichletSubspace S)
  let hν := ae_restrict_mem (μ := volume) hS.measurableSet
  let hV := dirichletSubspace_sobolev S
  have hs := hsuper M hM hB a r ℓ hr hball hshape hℓ hlow hupp hg w hm g τ η hη
  let T₀ := Physical.galerkinWeightedTestData hS hν hV X hX g (ρ.scaled η) w H
    τStar τ Csuper M.maxDiameter hτ hs
  let T : Section4.WeightedTest hS hν hV (Physical.conformingReconstruction _ X hX)
      g (ρ.scaled η) w τ Ctime Csuper M.maxDiameter := {
    op := T₀.op
    derivative := T₀.derivative
    endpoint := T₀.endpoint
    hasDeriv := T₀.hasDeriv
    symmetric := T₀.symmetric
    nonneg := T₀.nonneg
    time_bound := by
      intro z t ht
      have hb := T₀.time_bound z t ht
      simp only [SpatialProfile.scaled,hη,one_mul] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp only [Ctime]; linarith) (sq_nonneg _))
    superapprox := T₀.superapprox }
  exact ⟨T,rfl,rfl⟩

end Carleman
