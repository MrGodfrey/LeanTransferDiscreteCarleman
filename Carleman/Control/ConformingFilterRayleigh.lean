module

public import Carleman.Control.FilterRayleighBound
public import Carleman.Control.GalerkinStiffness
public import Carleman.Spatial.ConformingUniformInverse
public import Carleman.Spatial.DirichletScalarForm

/-! The original P1 coarse-space Rayleigh estimate in the fine space's
actual consistent L² mass and genuine Dirichlet Galerkin stiffness. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def nestedConformingFilter (X Y : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
    (hYX : Y ≤ X) : Submodule ℝ X := (Submodule.inclusion hYX).range

theorem dirichlet_galerkin_energy (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S) (x : X) :
    inner ℝ (galerkinStiffness (boundedDirichletOriginalForm hS hd hb) X hX x) x =
      ‖WeakSobolevJet.field 1 (domainSobolevJet hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) (Submodule.inclusion hX x))‖^2 := by
  exact (galerkinStiffness_form (boundedDirichletOriginalForm hS hd hb) X hX x x).trans
    ((dirichlet_scalarForm_canonical hS hd hb (Submodule.inclusion hX x) (Submodule.inclusion hX x)).trans
      (by rw [weakGradientPairing_apply,real_inner_self_eq_norm_sq]))

theorem nested_p1_filter_rayleigh (d : ℕ) (hd : 0 < d)
    (κ Q : ℝ) (hκ : 0 < κ) (hQ : 0 < Q) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (S : Set (SpatialCoordinates d))
      (hS : IsOpen S) (_hc : Convex ℝ S) (hb : Bornology.IsBounded S),
    ∀ [IsFiniteMeasure (volume.restrict S)] (M : SimplicialPartition S ι), S.Nonempty →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, M.maxDiameter ≤ Q*M.cellDiameter i) →
    ∀ (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
      (hX : X ≤ dirichletSubspace S) (hcoarse : M.conformingSpace (dirichletSubspace S) ≤ X),
      filterRayleigh (galerkinStiffness (boundedDirichletOriginalForm hS hd hb) X hX)
        (nestedConformingFilter X (M.conformingSpace (dirichletSubspace S)) hcoarse) ≤ C/M.maxDiameter^2 := by
  obtain ⟨C,hC,hbound⟩ := conforming_uniform_inverse d κ Q hκ hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS hc hb _ M hne a r hr hball hshape hquasi X _ hX hcoarse
  have hH := M.maxDiameter_pos hd hne
  apply filterRayleigh_le_of_energy_bound _ _ (by positivity)
  intro x hx
  obtain ⟨y,hy⟩ := hx
  let u := domainSobolevJet hS (ae_restrict_mem hS.measurableSet)
    (dirichletSubspace_sobolev S) (Submodule.inclusion hX x)
  have hu : WeakSobolevJet.value u = (x : Lp ℝ 2 (volume.restrict S)) := domainSobolevJet_value _ _ _ _
  have hmem : WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) := by
    rw [hu,← hy]
    exact y.property
  have hn := hbound ι S M hS hc a r hr hball hshape hquasi hH (dirichletSubspace S) u hmem
  rw [hu] at hn
  rw [dirichlet_galerkin_energy]
  change ‖WeakSobolevJet.field 1 u‖^2 ≤ (C^2/M.maxDiameter^2)*‖x‖^2
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  exact hs.trans_eq (by simp only [mul_pow,div_pow]; rfl)

theorem p1_coarse_filter_rayleigh (d : ℕ) (hd : 0 < d)
    (κ Q : ℝ) (hκ : 0 < κ) (hQ : 0 < Q) :
    ∃ C > (0:ℝ), ∀ (ι ιh : Type*) [Fintype ι] [Fintype ιh]
      (S : Set (SpatialCoordinates d)) (hS : IsOpen S) (_hc : Convex ℝ S) (hb : Bornology.IsBounded S),
    ∀ [IsFiniteMeasure (volume.restrict S)]
      (M : SimplicialPartition S ι) (Mh : SimplicialPartition S ιh), S.Nonempty →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, M.maxDiameter ≤ Q*M.cellDiameter i) →
    ∀ (hcoarse : M.conformingSpace (dirichletSubspace S) ≤ Mh.conformingSpace (dirichletSubspace S)),
      filterRayleigh (galerkinStiffness (boundedDirichletOriginalForm hS hd hb)
        (Mh.conformingSpace (dirichletSubspace S)) (Mh.conformingSpace_le (dirichletSubspace S)))
        (nestedConformingFilter (Mh.conformingSpace (dirichletSubspace S))
          (M.conformingSpace (dirichletSubspace S)) hcoarse) ≤ C/M.maxDiameter^2 := by
  obtain ⟨C,hC,hbnd⟩ := nested_p1_filter_rayleigh d hd κ Q hκ hQ
  refine ⟨C,hC,?_⟩
  intro ι ιh _ _ S hS hc hb _ M Mh hne a r hr hball hshape hquasi hcoarse
  exact hbnd ι S hS hc hb M hne a r hr hball hshape hquasi
    (Mh.conformingSpace (dirichletSubspace S)) (Mh.conformingSpace_le (dirichletSubspace S)) hcoarse

end Carleman.Physical
