module

public import Carleman.Spatial.SmoothDirectionalCalculus
public import Carleman.Spatial.SpatialTestOperations
public import Carleman.Spatial.TestPoincare
public import Carleman.Spatial.SobolevTruncation
public import Carleman.Spatial.SpatialTestDerivative
public import Carleman.Spatial.DerivativeFieldAssembly
public import Carleman.Weights.CoordinateDerivatives

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
namespace SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem eq_of_value_eq {φ ψ : SpatialTest S} (he : φ.value=ψ.value) : φ=ψ := by
  cases φ
  cases ψ
  cases he
  rfl

def wordTest (φ : SpatialTest S) : List (Fin d) → SpatialTest S
  | [] => φ
  | i::l => (wordTest φ l).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem wordTest_perm (φ : SpatialTest S) {l r : List (Fin d)} (h : l.Perm r) :
    φ.wordTest l=φ.wordTest r := by
  induction h with
  | nil => rfl
  | cons i h ih => exact congrArg (fun ψ : SpatialTest S => ψ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)) ih
  | swap i j l =>
    apply eq_of_value_eq
    funext x
    exact smoothD_comm (φ.wordTest l).smooth _ _ x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def multiTest (φ : SpatialTest S) {k : ℕ} (α : Sym (Fin d) k) : SpatialTest S :=
  φ.wordTest ((α : Multiset (Fin d)).sort (· ≤ ·))

theorem multiTest_nil (φ : SpatialTest S) : φ.multiTest Sym.nil=φ := by
  change φ.wordTest ((0 : Multiset (Fin d)).sort (· ≤ ·))=φ
  rw [Multiset.sort_zero]
  rfl

theorem multiTest_cons (φ : SpatialTest S) {k : ℕ} (α : Sym (Fin d) k) (i : Fin d) :
    φ.multiTest (Sym.cons i α)=(φ.multiTest α).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  change φ.wordTest ((↑(Sym.cons i α) : Multiset (Fin d)).sort (· ≤ ·))=
    φ.wordTest (i::(α : Multiset (Fin d)).sort (· ≤ ·))
  apply wordTest_perm
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq]
  change i ::ₘ (α : Multiset (Fin d))=i ::ₘ ((α : Multiset (Fin d)).sort (· ≤ ·) : List (Fin d))
  rw [Multiset.sort_eq]

set_option backward.isDefEq.respectTransparency true in
def allOrderJet (φ : SpatialTest S) (m : ℕ) : WeakSobolevJet d m (volume.restrict S) S := by
  refine ⟨fun k => derivativeFieldAssembly (fun α : Sym (Fin d) k.val => (φ.multiTest α).toLp (volume.restrict S)),?_⟩
  intro k α i
  dsimp only
  rw [derivativeFieldAssembly_component,derivativeFieldAssembly_component,multiTest_cons,derivativeTest_toLp]
  exact (φ.multiTest α).weakDerivative (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem allOrderJet_value (φ : SpatialTest S) (m : ℕ) :
    WeakSobolevJet.value (φ.allOrderJet m)=φ.toLp (volume.restrict S) := by
  change derivativeComponent Sym.nil (derivativeFieldAssembly _)=_
  rw [derivativeFieldAssembly_component,multiTest_nil]

theorem allOrderJet_component (φ : SpatialTest S) (m : ℕ) (k : Fin (m+1))
    (α : Sym (Fin d) k.val) :
    derivativeComponent α (WeakSobolevJet.field k (φ.allOrderJet m))=(φ.multiTest α).toLp (volume.restrict S) :=
  derivativeFieldAssembly_component _ _

theorem allOrderJet_truncate (φ : SpatialTest S) {m n : ℕ} (hm : m ≤ n) :
    WeakSobolevJet.truncate hm (φ.allOrderJet n)=φ.allOrderJet m := rfl

theorem allOrderJet_one (hS : IsOpen S) (φ : SpatialTest S) :
    φ.allOrderJet 1=φ.sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [allOrderJet_value,sobolevJet_value]

theorem zeroTest_allOrderJet (hS : IsOpen S) (m : ℕ) :
    (zeroTest (S := S)).allOrderJet m=0 := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [allOrderJet_value,map_zero]
  have he := congrArg WeakSobolevJet.value (zeroTest_jet hS)
  simpa only [sobolevJet_value,map_zero] using he

theorem addTest_allOrderJet (hS : IsOpen S) (φ ψ : SpatialTest S) (m : ℕ) :
    (φ.addTest ψ).allOrderJet m=φ.allOrderJet m+ψ.allOrderJet m := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  simp only [allOrderJet_value,map_add]
  have he := congrArg WeakSobolevJet.value (φ.addTest_jet hS ψ)
  simpa only [sobolevJet_value,map_add] using he

theorem smulTest_allOrderJet (hS : IsOpen S) (φ : SpatialTest S) (c : ℝ) (m : ℕ) :
    (φ.smulTest c).allOrderJet m=c • φ.allOrderJet m := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  simp only [allOrderJet_value,map_smul]
  have he := congrArg WeakSobolevJet.value (φ.smulTest_jet hS c)
  simpa only [sobolevJet_value,map_smul] using he

end SpatialTest
end Carleman
