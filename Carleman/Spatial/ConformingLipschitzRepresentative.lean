module

public import Carleman.Spatial.BoundedWeakGradient
public import Carleman.Spatial.DirichletZeroExtension
public import Carleman.Spatial.ConformingLocalPolynomial
public import Carleman.Spatial.NodalWeightedNorm

/-! The full conforming piecewise affine H¹₀ space has genuine global Lipschitz
representatives. The auxiliary bound may depend on the state and the mesh. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem conforming_gradient_bounded (hS : IsOpen S) (hc : Convex ℝ S)
    (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ M.conformingSpace V) :
    ∃ B : ℝ≥0, ∀ᵐ x ∂volume.restrict S, ‖WeakSobolevJet.field 1 u x‖ ≤ B := by
  classical
  choose p _ hg using M.conforming_local_polynomial hS hc V u hu
  let b := fun i => ‖derivativeOneFiber (affineScalarDerivative (p i))‖
  have hb : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨⟨∑ i, b i,hb⟩,M.ae_of_cells hS hc (fun i => ?_)⟩
  filter_upwards [hg i] with x hx
  rw [hx,(affineScalar_hasFDerivAt (p i) x).fderiv]
  exact Finset.single_le_sum (fun j _ => norm_nonneg (derivativeOneFiber (affineScalarDerivative (p j))))
    (Finset.mem_univ i)

theorem conforming_dirichlet_lipschitz_representative (hS : IsOpen S) (hc : Convex ℝ S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (hp : WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S)) :
    ∃ C : ℝ≥0, ∃ f : SpatialCoordinates d → ℝ, LipschitzWith C f ∧
      zeroExtendLp hS.measurableSet (WeakSobolevJet.value u) =ᵐ[volume] f := by
  obtain ⟨B,hB⟩ := M.conforming_gradient_bounded hS hc (dirichletSubspace S) u hp
  let v := fun i : Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
  have hv (i : Fin d) : IsWeakSpatialDerivative volume univ
      (EuclideanSpace.basisFun (Fin d) ℝ i)
      (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) (v i) :=
    dirichlet_zeroExtend_weak_derivative hS u hu i
  have hb (i : Fin d) : ∀ᵐ x ∂volume, ‖v i x‖ ≤ B := by
    have hd : ∀ᵐ x ∂volume.restrict S,
        ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x‖ ≤ B := by
      filter_upwards [hB,derivativeComponent_ae (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)] with x hx hy
      rw [hy]
      exact (PiLp.norm_apply_le _ _).trans hx
    filter_upwards [zeroExtendLp_ae hS.measurableSet
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)),
      (ae_restrict_iff' hS.measurableSet).mp hd] with x hx hy
    change ‖zeroExtendLp hS.measurableSet _ x‖ ≤ _
    rw [hx]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      exact hy hxS
    · simp only [indicator_of_notMem hxS,norm_zero]
      exact B.property
  obtain ⟨f,hf,he⟩ := exists_lipschitzRepresentative_of_bounded_weak_derivatives
    (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) v hv B hb
  exact ⟨d*B,f,hf,he⟩

end Carleman.SimplicialPartition
