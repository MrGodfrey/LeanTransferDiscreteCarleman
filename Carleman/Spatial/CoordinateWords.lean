module

public import Carleman.Spatial.SobolevTopology
public import Carleman.Spatial.WeakProduct
public import Carleman.Weights.CoordinateDerivatives

/-! Ordered coordinate words access the existing symmetric weak derivative
collections. Ordering is used only to perform induction; no new derivative
norm or restriction on states is introduced. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman

def wordIndex {d : ℕ} (l : List (Fin d)) : Sym (Fin d) l.length :=
  ⟨(l : Multiset (Fin d)), rfl⟩

theorem wordIndex_cons {d : ℕ} (i : Fin d) (l : List (Fin d)) :
    wordIndex (i::l) = Sym.cons i (wordIndex l) := rfl

namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def wordField (u : WeakSobolevJet d n ν S) (l : List (Fin d)) : Lp ℝ 2 ν :=
  if h : l.length ≤ n then derivativeComponent (wordIndex l) (field ⟨l.length, by omega⟩ u) else 0

theorem wordField_nil (u : WeakSobolevJet d n ν S) : wordField u [] = value u := by
  simp only [wordField, List.length_nil, Nat.zero_le, dite_true]
  rfl

theorem wordField_weak (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (i : Fin d)
    (hl : l.length < n) :
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (wordField u l) (wordField u (i::l)) := by
  simp only [wordField, List.length_cons, dite_eq_left (Nat.le_of_lt hl), dite_eq_left (by omega : l.length+1 ≤ n), wordIndex_cons]
  exact u.property ⟨l.length, hl⟩ (wordIndex l) i

theorem wordField_norm_le (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n) :
    ‖wordField u l‖ ≤ ‖field ⟨l.length, by omega⟩ u‖ := by
  rw [wordField, dite_eq_left hl]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [derivativeComponent_ae (wordIndex l) (field ⟨l.length, by omega⟩ u)] with x hx
  rw [hx]
  exact PiLp.norm_apply_le _ _
end WeakSobolevJet

namespace IsWeakSpatialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsFiniteMeasureOnCompacts ν] {S : Set E} {e : E}

theorem list_sum {ι : Type*} (l : List ι) (u v : ι → Lp ℝ 2 ν)
    (h : ∀ i ∈ l, IsWeakSpatialDerivative ν S e (u i) (v i)) :
    IsWeakSpatialDerivative ν S e (l.map u).sum (l.map v).sum := by
  induction l with
  | nil => exact IsWeakSpatialDerivative.zero
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))
end IsWeakSpatialDerivative

/-- Each derivative chooses the multiplier or the state factor; multiplicities
are retained, so this is the genuine Leibniz expansion. -/
def derivativeSplits {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i::l => (derivativeSplits l).map (fun p => (i::p.1, p.2)) ++
      (derivativeSplits l).map (fun p => (p.1, i::p.2))

theorem derivativeSplits_lengths {ι : Type*} (l : List ι) (p : List ι × List ι)
    (hp : p ∈ derivativeSplits l) : p.1.length + p.2.length = l.length := by
  induction l generalizing p with
  | nil =>
    have he : p = ([], []) := by simpa [derivativeSplits] using hp
    subst p
    rfl
  | cons i l ih =>
    simp only [derivativeSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simpa only [List.length_cons] using (by
      have hh := ih q hq
      omega : _)

theorem derivativeSplits_length {ι : Type*} (l : List ι) : (derivativeSplits l).length = 2^l.length := by
  induction l with
  | nil => simp [derivativeSplits]
  | cons i l ih => simp [derivativeSplits, ih, pow_succ, Nat.mul_comm, two_mul]

end Carleman
