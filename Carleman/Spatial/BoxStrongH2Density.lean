module
public import Carleman.Spatial.SpatialTestAllOrders
public import Carleman.Spatial.SobolevRestriction
public import Carleman.Spatial.SmoothLaplacianL2Limit
public import Carleman.Spatial.SmoothBoundaryDirichlet
/-! Actual component limits assemble the full H² graph topology, with genuine
zero-boundary smooth approximation on the original coordinate box. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d k m : ℕ} {S : Set (SpatialCoordinates d)} {ν : Measure (SpatialCoordinates d)}

theorem derivativeFieldAssembly_components (u : Lp (DerivativeFiber d k) 2 ν) :
    derivativeFieldAssembly (fun α => derivativeComponent α u)=u := by
  apply derivativeComponent_ext
  intro α
  exact derivativeFieldAssembly_component _ α

theorem derivativeField_tendsto_of_components
    {U : ℕ → Lp (DerivativeFiber d k) 2 ν} {u : Lp (DerivativeFiber d k) 2 ν}
    (ht : ∀ α, Tendsto (fun n => derivativeComponent α (U n)) atTop
      (𝓝 (derivativeComponent α u))) : Tendsto U atTop (𝓝 u) := by
  have h := (derivativeFieldAssembly.continuous.tendsto (fun α => derivativeComponent α u)).comp
    (tendsto_pi_nhds.mpr ht)
  change Tendsto (fun n => derivativeFieldAssembly (fun α => derivativeComponent α (U n))) atTop (𝓝 _) at h
  simpa only [derivativeFieldAssembly_components] using h

theorem WeakSobolevJet.tendsto_of_components [IsFiniteMeasureOnCompacts ν]
    {U : ℕ → WeakSobolevJet d m ν S} {u : WeakSobolevJet d m ν S}
    (ht : ∀ (k : Fin (m+1)) (α : Sym (Fin d) k.val),
      Tendsto (fun n => derivativeComponent α (field k (U n))) atTop
        (𝓝 (derivativeComponent α (field k u)))) : Tendsto U atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  exact derivativeField_tendsto_of_components (ht k)

namespace SpatialTest

def allOrderJetOn (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (m : ℕ) : WeakSobolevJet d m (volume.restrict S) S :=
  WeakSobolevJet.restrictSubdomain (subset_univ S) (φ.allOrderJet m)

theorem allOrderJetOn_component (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (m : ℕ) (k : Fin (m+1)) (α : Sym (Fin d) k.val) :
    derivativeComponent α (WeakSobolevJet.field k (φ.allOrderJetOn S m))=
      (φ.multiTest α).toLp (volume.restrict S) := by
  change derivativeComponent α (subdomainLp (subset_univ S) (WeakSobolevJet.field k (φ.allOrderJet m)))=_
  rw [derivativeComponent_subdomain,allOrderJet_component]
  apply Lp.ext
  exact (subdomainLp_ae (subset_univ S) _).trans
    (((φ.multiTest α).toLp_ae (volume.restrict univ)).filter_mono
      (ae_mono (Measure.restrict_mono (subset_univ S) le_rfl)) |>.trans
      ((φ.multiTest α).toLp_ae (volume.restrict S)).symm)

theorem allOrderJetOn_value (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (m : ℕ) :
    WeakSobolevJet.value (φ.allOrderJetOn S m)=φ.toLp (volume.restrict S) := by
  exact (allOrderJetOn_component φ S m 0 Sym.nil).trans
    (congrArg (fun t : SpatialTest univ => t.toLp (volume.restrict S)) (multiTest_nil φ))

theorem allOrderJetOn_component_one_ae (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (v : Fin 1 → Fin d) :
    derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 (φ.allOrderJetOn S 2))
      =ᵐ[volume.restrict S] coordinateDerivative v φ.value := by
  rw [allOrderJetOn_component φ S 2 1 (Sym.cons (v 0) Sym.nil),multiTest_cons,multiTest_nil,derivativeTest_toLp]
  exact (φ.derivativeLp_ae (volume.restrict S) _).trans
    (Eventually.of_forall fun x => (coordinateDerivative_one v φ.value x).symm)

theorem allOrderJetOn_component_two_ae (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (v : Fin 2 → Fin d) :
    derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil))
      (WeakSobolevJet.field 2 (φ.allOrderJetOn S 2))
      =ᵐ[volume.restrict S] coordinateDerivative v φ.value := by
  rw [allOrderJetOn_component φ S 2 2 (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)),multiTest_cons,multiTest_cons,multiTest_nil,derivativeTest_toLp]
  filter_upwards [(φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ (v 0))).derivativeLp_ae
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ (v 1))] with x hx
  rw [hx,coordinateDerivative_two,iteratedFDeriv_two_apply]
  have hdf : ContDiff ℝ 1 (fderiv ℝ φ.value) := φ.smooth.fderiv_right (by simp)
  have he := fderiv_clm_apply (hdf.differentiable (by simp) x)
    (differentiableAt_const (EuclideanSpace.basisFun (Fin d) ℝ (v 0)))
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add] at he
  change fderiv ℝ (fun y => fderiv ℝ φ.value y (EuclideanSpace.basisFun (Fin d) ℝ (v 0))) x
    (EuclideanSpace.basisFun (Fin d) ℝ (v 1)) =
    fderiv ℝ (fderiv ℝ φ.value) x (EuclideanSpace.basisFun (Fin d) ℝ (v 0))
      (EuclideanSpace.basisFun (Fin d) ℝ (v 1))
  rw [he]
  exact (φ.smooth.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

theorem allOrderJetOn_dirichlet (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (hzero : ∀ x∈frontier S, φ.value x=0) :
    WeakSobolevJet.truncate (by decide : 1≤2) (φ.allOrderJetOn S 2)∈dirichletJetSpace S := by
  apply smooth_boundary_zero_mem_dirichletJetSpace hS hc hb hne φ hzero
  rw [WeakSobolevJet.truncate_value,allOrderJetOn_value]
  exact φ.toLp_ae _

theorem allOrderJetOn_two_tendsto_of_errors
    (U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)))
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (h0 : Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => (U n).value x-WeakSobolevJet.value u x)) atTop (𝓝 0))
    (h1 : ∀ v : Fin 1 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => coordinateDerivative v (U n).value x-
        derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u) x)) atTop (𝓝 0))
    (h2 : ∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict S)
      (fun x => coordinateDerivative v (U n).value x-
        derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u) x)) atTop (𝓝 0)) :
    Tendsto (fun n => (U n).allOrderJetOn S 2) atTop (𝓝 u) := by
  apply WeakSobolevJet.tendsto_of_components
  intro k α
  fin_cases k
  · have ha := Sym.eq_nil_of_card_zero α
    subst α
    change Tendsto (fun n => WeakSobolevJet.value ((U n).allOrderJetOn S 2)) atTop (𝓝 (WeakSobolevJet.value u))
    apply lp_tendsto_of_representative_L2_error _ _ (fun n => (U n).value) _ h0
    intro n
    rw [allOrderJetOn_value]
    exact (U n).toLp_ae _
  · obtain ⟨i,β,rfl⟩ := Sym.exists_eq_cons_of_succ α
    have hb := Sym.eq_nil_of_card_zero β
    subst β
    apply lp_tendsto_of_representative_L2_error _ _ (fun n => coordinateDerivative ![i] (U n).value)
    · intro n
      exact (U n).allOrderJetOn_component_one_ae S ![i]
    · exact h1 ![i]
  · obtain ⟨j,β,rfl⟩ := Sym.exists_eq_cons_of_succ α
    obtain ⟨i,γ,rfl⟩ := Sym.exists_eq_cons_of_succ β
    have hc := Sym.eq_nil_of_card_zero γ
    subst γ
    apply lp_tendsto_of_representative_L2_error _ _ (fun n => coordinateDerivative ![i,j] (U n).value)
    · intro n
      exact (U n).allOrderJetOn_component_two_ae S ![i,j]
    · exact h2 ![i,j]
end SpatialTest

theorem exists_box_dirichlet_strong_h2_approximation (a b : Fin d → ℝ)
    (hpos : ∀ i, a i<b i)
    (u : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : WeakSobolevJet.truncate (by decide : 1≤2) u∈dirichletJetSpace (openCoordinateBox a b)) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier (openCoordinateBox a b), (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2) ((U n).allOrderJetOn (openCoordinateBox a b) 2)∈
        dirichletJetSpace (openCoordinateBox a b)) ∧
      Tendsto (fun n => (U n).allOrderJetOn (openCoordinateBox a b) 2) atTop (𝓝 u) := by
  obtain ⟨U,hb,h0,h1,h2⟩ := exists_box_dirichlet_compact_h2_approximation a b hpos u hu
  refine ⟨U,hb,?_,SpatialTest.allOrderJetOn_two_tendsto_of_errors U u h0 h1 h2⟩
  intro n
  exact (U n).allOrderJetOn_dirichlet (openCoordinateBox_isOpen a b)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) (hb n)
end Carleman
