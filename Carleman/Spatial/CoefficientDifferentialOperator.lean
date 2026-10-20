module

public import Carleman.Spatial.CoefficientDifferentialTerm
public import Carleman.Spatial.HigherCoefficientForm
public import Carleman.Spatial.ComponentNorms

/-! The full distributional coefficient expression is the actual operator
associated with the original H₀ᵐ form, not a substituted operator. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators
namespace Carleman
variable {d n m : ℕ} {S : Set (SpatialCoordinates d)}
namespace WeakSobolevJet
variable [IsFiniteMeasure (volume.restrict S)]

omit [IsFiniteMeasure (volume.restrict S)] in
theorem wordField_multiIndex_truncate (u : WeakSobolevJet d n (volume.restrict S) S)
    (hmn : m ≤ n) (α : MultiDerivativeIndex d m) :
    wordField u (coordinateVector α.2).toList=jetScalarComponent α (truncate hmn u) := by
  rw [wordField_vector u (by omega : α.1.val ≤ n),coordinateVector_represents]
  rfl

end WeakSobolevJet

variable [IsFiniteMeasure (volume.restrict S)]

def coefficientDifferentialOperator
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (u : WeakSobolevJet d (2*m) (volume.restrict S) S) : Lp ℝ 2 (volume.restrict S) :=
  ∑ α, ∑ β, (-1:ℝ)^α.1.val • WeakSobolevJet.coefficientDifferentialTerm (a α β) u
    (coordinateVector α.2).toList (coordinateVector β.2).toList

theorem coefficientDifferentialOperator_test (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (u : WeakSobolevJet d (2*m) (volume.restrict S) S) (φ : SpatialTest S) :
    inner ℝ (coefficientDifferentialOperator a u) (φ.toLp (volume.restrict S))=
      coefficientJetForm (fun α β => (a α β).derivative [])
        (WeakSobolevJet.truncate (by omega : m ≤ 2*m) u) (φ.allOrderJet m) := by
  simp only [coefficientDifferentialOperator,sum_inner,real_inner_smul_left,coefficientJetForm_apply]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [WeakSobolevJet.coefficientDifferentialTerm_test hS (a α β) u _ _
    (by simp only [List.Vector.toList_length]; omega),List.Vector.toList_length,
    ←mul_assoc,←mul_pow]
  norm_num only [neg_mul_neg,one_mul,one_pow]
  rw [WeakSobolevJet.wordField_multiIndex_truncate u (by omega : m ≤ 2*m)]
  change inner ℝ _ ((φ.multiTest α.2).toLp (volume.restrict S))=inner ℝ _
    (derivativeComponent α.2 (WeakSobolevJet.field α.1 (φ.allOrderJet m)))
  rw [φ.allOrderJet_component]

theorem coefficientDifferentialOperator_form (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (u : WeakSobolevJet d (2*m) (volume.restrict S) S)
    (v : WeakSobolevJet d m (volume.restrict S) S) (hv : v ∈ higherDirichletJetSpace S m) :
    inner ℝ (coefficientDifferentialOperator a u) (WeakSobolevJet.value v)=
      coefficientJetForm (fun α β => (a α β).derivative [])
        (WeakSobolevJet.truncate (by omega : m ≤ 2*m) u) v := by
  have hc : IsClosed {v : WeakSobolevJet d m (volume.restrict S) S |
      inner ℝ (coefficientDifferentialOperator a u) (WeakSobolevJet.value v)=
        coefficientJetForm (fun α β => (a α β).derivative [])
          (WeakSobolevJet.truncate (by omega : m ≤ 2*m) u) v} :=
    isClosed_eq (continuous_const.inner WeakSobolevJet.valueCLM.continuous)
      (coefficientJetForm _ _).continuous
  change v ∈ (higherDirichletJetSpace S m : Set _) at hv
  rw [higherDirichletJetSpace_eq_closure S m hS] at hv
  apply closure_minimal _ hc hv
  rintro _ ⟨φ,rfl⟩
  change inner ℝ _ (WeakSobolevJet.value (φ.allOrderJet m))=_
  rw [φ.allOrderJet_value]
  exact coefficientDifferentialOperator_test hS a u φ

theorem higherCoefficient_operator_graph_of_sobolev (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (u : WeakSobolevJet d (2*m) (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ higherDirichletSubspace S m) :
    ∃ z : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain,
      (z : Lp ℝ 2 (volume.restrict S))=WeakSobolevJet.value u ∧
      (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator z=
        coefficientDifferentialOperator a u := by
  rw [(higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator_isAssociated]
  let v := WeakSobolevJet.truncate (by omega : m ≤ 2*m) u
  refine ⟨⟨SobolevHilbert.ofJet v,hu⟩,rfl,?_⟩
  intro w
  exact (coefficientDifferentialOperator_form hS a u (higherDirichletToJet S m w)
    ((mem_higherDirichletJetSpace_iff S m hS _).mpr w.property)).symm

theorem higherCoefficient_operator_eq_differential (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (z : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain)
    (u : WeakSobolevJet d (2*m) (volume.restrict S) S)
    (hu : WeakSobolevJet.value u=(z : Lp ℝ 2 (volume.restrict S))) :
    (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator z=
      coefficientDifferentialOperator a u := by
  have hV : WeakSobolevJet.value u ∈ higherDirichletSubspace S m := by
    rw [hu]
    exact (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).domain_le z.property
  obtain ⟨z',hz',hop⟩ := higherCoefficient_operator_graph_of_sobolev hS a hsym hcoer u hV
  have he : z'=z := Subtype.ext (hz'.trans hu)
  rwa [he] at hop

theorem higherCoefficient_operator_domain_eq (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (hreg : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain ≤
      sobolevSubspace d (2*m) (volume.restrict S) S) :
    (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain=
      higherDirichletSubspace S m ⊓ sobolevSubspace d (2*m) (volume.restrict S) S := by
  ext x
  constructor
  · intro hx
    exact ⟨(higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).domain_le hx,hreg hx⟩
  · rintro ⟨hx,u,hu⟩
    obtain ⟨z,hz,_⟩ := higherCoefficient_operator_graph_of_sobolev hS a hsym hcoer u (by rw [hu]; exact hx)
    have he : (z : Lp ℝ 2 (volume.restrict S))=x := hz.trans hu
    exact he ▸ z.property

theorem higherCoefficient_operator_canonical (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (hreg : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain ≤
      sobolevSubspace d (2*m) (volume.restrict S) S)
    (z : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain) :
    (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator z=
      coefficientDifferentialOperator a (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hreg z) :=
  higherCoefficient_operator_eq_differential hS a hsym hcoer z _
    (domainSobolevJet_value hS (ae_restrict_mem hS.measurableSet) hreg z)

end Carleman
