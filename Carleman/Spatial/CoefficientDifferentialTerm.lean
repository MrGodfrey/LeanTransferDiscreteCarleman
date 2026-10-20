module

public import Carleman.Spatial.WeakCoefficientJet
public import Carleman.Spatial.SpatialTestAllOrders

/-! Every finite coefficient term is the actual weak derivative of a D^βu,
with exact repeated integration by parts and all Leibniz multiplicities. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators
namespace Carleman
variable {d n m : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.wordTest_append (φ : SpatialTest S) (l r : List (Fin d)) :
    φ.wordTest (l++r)=(φ.wordTest r).wordTest l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append,SpatialTest.wordTest,ih]

theorem SpatialTest.wordTest_derivativeTest (φ : SpatialTest S) (l : List (Fin d)) (i : Fin d) :
    (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).wordTest l=
      φ.wordTest (i::l) := by
  change (φ.wordTest [i]).wordTest l=_
  rw [←φ.wordTest_append]
  exact φ.wordTest_perm (List.perm_append_singleton i l)

/-- Repeated integration by parts for an actual finite distributional chain. -/
theorem weakWordChain_test
    (U : List (Fin d) → Lp ℝ 2 (volume.restrict S))
    (hU : ∀ l i, l.length < n → IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) (U l) (U (i::l)))
    (l : List (Fin d)) (hl : l.length ≤ n) (φ : SpatialTest S) :
    inner ℝ (U l) (φ.toLp (volume.restrict S))=
      (-1:ℝ)^l.length*inner ℝ (U []) ((φ.wordTest l).toLp (volume.restrict S)) := by
  induction l generalizing φ with
  | nil => simp only [List.length_nil,pow_zero,one_mul,SpatialTest.wordTest]
  | cons i l ih =>
    have hln : l.length < n := by simp only [List.length_cons] at hl; omega
    have hh := hU l i hln φ
    have he := ih (by omega) (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i))
    rw [SpatialTest.derivativeTest_toLp,SpatialTest.wordTest_derivativeTest] at he
    rw [List.length_cons,pow_succ]
    linarith only [hh,he]

namespace WeakSobolevJet
variable [IsFiniteMeasure (volume.restrict S)]

def coefficientDifferentialTerm (a : BoundedWeakCoefficient S n)
    (u : WeakSobolevJet d n (volume.restrict S) S) (l r : List (Fin d)) : Lp ℝ 2 (volume.restrict S) :=
  ((derivativeSplits l).map (fun p => (a.derivative p.1).map (wordField u (p.2++r)))).sum

omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientDifferentialTerm_nil (a : BoundedWeakCoefficient S n)
    (u : WeakSobolevJet d n (volume.restrict S) S) (r : List (Fin d)) :
    coefficientDifferentialTerm a u [] r=(a.derivative []).map (wordField u r) := by
  simp [coefficientDifferentialTerm,derivativeSplits]

theorem coefficientDifferentialTerm_weak (hS : IsOpen S) (a : BoundedWeakCoefficient S n)
    (u : WeakSobolevJet d n (volume.restrict S) S) (l r : List (Fin d)) (i : Fin d)
    (hl : l.length+r.length < n) :
    IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (coefficientDifferentialTerm a u l r) (coefficientDifferentialTerm a u (i::l) r) := by
  have hh := IsWeakSpatialDerivative.list_sum (derivativeSplits l)
    (fun p => (a.derivative p.1).map (wordField u (p.2++r)))
    (fun p => (a.derivative p.1).map (wordField u (i::(p.2++r)))+
      (a.derivative (i::p.1)).map (wordField u (p.2++r))) (by
      intro p hp
      have hlen := derivativeSplits_lengths l p hp
      exact (wordField_weak u (p.2++r) i (by simp only [List.length_append]; omega)).mul_weakCoefficient hS
        (a.derivative p.1) (a.derivative (i::p.1)) (a.weak_derivative p.1 i (by omega)))
  change IsWeakSpatialDerivative (volume.restrict S) S _ (coefficientDifferentialTerm a u l r) _ at hh
  convert hh using 1
  simp only [coefficientDifferentialTerm,derivativeSplits,List.map_append,List.map_map,List.sum_append,
    List.sum_map_add]
  exact add_comm _ _

theorem coefficientDifferentialTerm_test (hS : IsOpen S) (a : BoundedWeakCoefficient S n)
    (u : WeakSobolevJet d n (volume.restrict S) S) (l r : List (Fin d))
    (hl : l.length+r.length ≤ n) (φ : SpatialTest S) :
    inner ℝ (coefficientDifferentialTerm a u l r) (φ.toLp (volume.restrict S))=
      (-1:ℝ)^l.length*inner ℝ ((a.derivative []).map (wordField u r))
        ((φ.wordTest l).toLp (volume.restrict S)) := by
  have he := weakWordChain_test (n := n-r.length) (fun t => coefficientDifferentialTerm a u t r)
    (fun t i ht => coefficientDifferentialTerm_weak hS a u t r i (by omega)) l (by omega) φ
  simpa only [coefficientDifferentialTerm_nil] using he
end WeakSobolevJet
end Carleman
