module

public import Carleman.Spatial.OddSlabSmoothing
public import Carleman.Spatial.LocalSmoothingRestriction
public import Carleman.Spatial.BoxPoissonRegularity

/-! Every original box H2 intersect H1_0 state has a global smooth, exactly
zero-boundary sequence converging in value and all actual derivatives through order two. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ}

theorem exists_box_dirichlet_smooth_h2_approximation (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i)
    (u : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : WeakSobolevJet.truncate (by decide : 1 ≤ 2) u ∈ dirichletJetSpace (openCoordinateBox a b)) :
    ∃ U : ℕ → SpatialCoordinates d → ℝ,
      (∀ n, ContDiff ℝ ∞ (U n)) ∧
      (∀ n, ∀ x ∈ frontier (openCoordinateBox a b), U n x=0) ∧
      Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => U n x-WeakSobolevJet.value u x)) atTop (𝓝 0) ∧
      (∀ v : Fin 1 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => coordinateDerivative v (U n) x-
          derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u) x)) atTop (𝓝 0)) ∧
      (∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => coordinateDerivative v (U n) x-
          derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u) x)) atTop (𝓝 0)) := by
  let S := openCoordinateBox a b
  let A := expandedBoxLower a b Finset.univ
  let B := expandedBoxUpper a b Finset.univ
  let T := openCoordinateBox A B
  have hS : IsOpen S := openCoordinateBox_isOpen a b
  have hT : IsOpen T := openCoordinateBox_isOpen A B
  have hST : S ⊆ T := expandedBox_contains a b Finset.univ
  have hK : IsCompact (closure S) := (openCoordinateBox_isBounded a b).isCompact_closure
  have hKT : closure S ⊆ T := expandedBox_closure_inside a b hpos
  obtain ⟨v,g,hv,_,hbdy⟩ := exists_box_poisson_extension_smooth_boundary a b hpos
    (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) hu (negativeLaplacian u) (negativeLaplacian_isWeak u)
  obtain ⟨_,_,hreg⟩ := exists_box_dirichlet_H2_bound A B (expandedBox_positive a b hpos Finset.univ)
  obtain ⟨w,hw,_,_⟩ := hreg v hv.1 g hv.2.1
  have hval : WeakSobolevJet.value w=WeakSobolevJet.value v := by
    rw [← WeakSobolevJet.truncate_value (by decide : 1 ≤ 2),hw]
  have hrest : WeakSobolevJet.restrictSubdomain hST w=u := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [WeakSobolevJet.restrictSubdomain_value,hval]
    have hh := congrArg WeakSobolevJet.value hv.2.2.1
    simpa only [WeakSobolevJet.restrictSubdomain_value,WeakSobolevJet.truncate_value] using hh
  let F := fun n => zeroExtendLp hT.measurableSet (WeakSobolevJet.value w)
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value
  have hlocal := WeakSobolevJet.local_even_mollification_strong_h2 hT hK hKT w
  change (∀ n, ContDiff ℝ ∞ (F n)) ∧ _ at hlocal
  rcases hlocal with ⟨hFs,h0,h1,h2⟩
  have hb : ∀ᶠ n in atTop, ∀ x ∈ frontier S, F n x=0 := by
    simpa only [F,hval] using hbdy
  have hv0 : WeakSobolevJet.value w =ᵐ[volume.restrict S] WeakSobolevJet.value u := by
    have he := congrArg WeakSobolevJet.value hrest
    rw [WeakSobolevJet.restrictSubdomain_value] at he
    exact (subdomainLp_ae hST _).symm.trans (Filter.Eventually.of_forall fun x => congrArg (fun z => z x) he)
  have ht0 := local_L2_error_restrict_tendsto hK subset_closure hKT
    (WeakSobolevJet.value w) (WeakSobolevJet.value u) hv0 F (fun n => (hFs n).continuous) h0
  have ht1 (v : Fin 1 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => coordinateDerivative v (F n) x-
        derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u) x)) atTop (𝓝 0) := by
    apply local_L2_error_restrict_tendsto hK subset_closure hKT
      (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 w)) _
      (WeakSobolevJet.restrictSubdomain_component_ae hST w u hrest 1 _) (fun n => coordinateDerivative v (F n))
      (fun n => (coordinateTensorEval v).continuous.comp ((hFs n).continuous_iteratedFDeriv (by simp)))
    simpa only [coordinateDerivative_one,F] using h1 (v 0)
  have ht2 (v : Fin 2 → Fin d) : Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => coordinateDerivative v (F n) x-
        derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u) x)) atTop (𝓝 0) := by
    apply local_L2_error_restrict_tendsto hK subset_closure hKT
      (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 w)) _
      (WeakSobolevJet.restrictSubdomain_component_ae hST w u hrest 2 _) (fun n => coordinateDerivative v (F n))
      (fun n => (coordinateTensorEval v).continuous.comp ((hFs n).continuous_iteratedFDeriv (by simp)))
    simpa only [coordinateDerivative_two,F] using h2 (v 0) (v 1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  refine ⟨fun n => F (n+N),fun n => hFs (n+N),fun n => hN (n+N) (Nat.le_add_left N n),
    ht0.comp (tendsto_add_atTop_nat N),fun v => (ht1 v).comp (tendsto_add_atTop_nat N),
    fun v => (ht2 v).comp (tendsto_add_atTop_nat N)⟩

end Carleman
