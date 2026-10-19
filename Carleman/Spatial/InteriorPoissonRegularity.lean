module

public import Carleman.Spatial.CutoffPoissonEstimate
public import Carleman.Spatial.CutoffMollifierGradient
public import Carleman.Spatial.InteriorSmoothCutoff
public import Carleman.Spatial.WeakH2BoundedLimit
public import Carleman.Spatial.WeakPoissonRestriction

/-! Interior H² regularity for the original H¹ weak Poisson solution.
A fixed cutoff supplies the estimates; actual strong gradient convergence
and the complete original test family recover its second weak derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution Topology BigOperators
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem exists_interior_H2_of_cutoff (hS : IsOpen S) (hT : IsOpen T)
    (hTS : T ⊆ S) (η : SpatialTest S) (hη : ∀ x ∈ T, η.value x = 1) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S)),
      IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict T) T,
        WeakSobolevJet.truncate (by decide : 1 ≤ 2) v = WeakSobolevJet.restrictSubdomain hTS u ∧
        ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*
          (M*(‖f‖ + 2*(∑ i : Fin d,
            ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) +
            ‖WeakSobolevJet.value u‖))^2 := by
  obtain ⟨M,hM,hb⟩ := η.exists_laplacian_multiplier_bound
  refine ⟨M,hM,?_⟩
  intro u f hu
  let φ := fun n => η.mulSmooth ((spatialMollifier d n).smooth_convolution
    (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)))
  let G := fun n i => subdomainLp hTS ((φ n).derivativeLp (volume.restrict S)
    (EuclideanSpace.basisFun (Fin d) ℝ i))
  let A := fun n i j => subdomainLp hTS
    (((φ n).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
      (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))
  let C := M*(‖f‖ + 2*(∑ i : Fin d,
    ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) + ‖WeakSobolevJet.value u‖)
  apply exists_weakH2_of_gradient_test_limits hT (WeakSobolevJet.restrictSubdomain hTS u) G A (C := C) (by positivity)
  · intro i j ψ
    exact (cutoff_mollifier_gradient_tendsto hS hT hTS η hη u i).inner tendsto_const_nhds
  · intro i j ψ
    apply Eventually.of_forall
    intro n
    have hw := ((φ n).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).weakDerivative
      (EuclideanSpace.basisFun (Fin d) ℝ j)
    rw [(φ n).derivativeTest_toLp] at hw
    exact hw.restrictSubdomain hTS ψ
  · intro i j
    filter_upwards [compact_mollifier_eventually_inside hS η.compact η.support] with n hn
    exact (subdomainLp_norm_le hTS _).trans
      (((φ n).hessian_component_norm_le_laplacian i j).trans
        (hu.cutoff_laplacian_bound hS.measurableSet η hM
          (fun x => (hb x).1) (fun i x => (hb x).2.1 i) (fun x => (hb x).2.2)
          (spatialMollifier d n) (spatialMollifier_nonneg n) (spatialMollifier_integral n) hn))

theorem exists_interior_H2_bound (hS : IsOpen S) (hT : IsOpen T)
    (hcompact : IsCompact (closure T)) (hclosure : closure T ⊆ S) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S)),
      IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict T) T,
        WeakSobolevJet.truncate (by decide : 1 ≤ 2) v =
          WeakSobolevJet.restrictSubdomain (subset_closure.trans hclosure) u ∧
        negativeLaplacian v = subdomainLp (subset_closure.trans hclosure) f ∧
        ‖WeakSobolevJet.field 2 v‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*
          (M*(‖f‖ + 2*(∑ i : Fin d,
            ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖) +
            ‖WeakSobolevJet.value u‖))^2 := by
  obtain ⟨η,hη⟩ := exists_spatialTest_eq_one_on_compact hS hcompact hclosure
  obtain ⟨M,hM,hbound⟩ := exists_interior_H2_of_cutoff hS hT (subset_closure.trans hclosure) η
    (fun x hx => hη x (subset_closure hx))
  refine ⟨M,hM,?_⟩
  intro u f hu
  obtain ⟨v,hv,hn⟩ := hbound u f hu
  refine ⟨v,hv,?_,hn⟩
  have hw := negativeLaplacian_isWeak v
  rw [hv] at hw
  exact hw.unique_rhs hT (hu.restrictSubdomain hS hT (subset_closure.trans hclosure))

end Carleman
