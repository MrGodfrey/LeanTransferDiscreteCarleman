module

public import Carleman.Spatial.CoordinateWords

/-! The full distributional Leibniz formula for every order, on actual L²
weak derivatives. The multiplier derivatives are linked by their true
Fréchet derivative identities. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)

def leibnizField (a : List (Fin d) → BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) : Lp ℝ 2 ν :=
  ((derivativeSplits l).map (fun p => (a p.1).map (wordField u p.2))).sum

omit [IsLocallyFiniteMeasure ν] in
theorem leibnizField_nil (a : List (Fin d) → BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) : leibnizField a u [] = (a []).map (value u) := by
  simp [leibnizField, derivativeSplits, wordField_nil]

include hS hν
omit [IsLocallyFiniteMeasure ν] in
/-- Differentiating the entire actual expansion gives the next expansion. -/
theorem leibnizField_weak (a : List (Fin d) → BoundedMultiplier ν)
    (ha : ∀ l, ContDiffOn ℝ ∞ (a l).value S)
    (hd : ∀ l i, (a (i::l)).value =ᵐ[ν]
      (fun x => fderiv ℝ (a l).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (i : Fin d) (hl : l.length < n) :
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (leibnizField a u l) (leibnizField a u (i::l)) := by
  have hh := IsWeakSpatialDerivative.list_sum (derivativeSplits l)
    (fun p => (a p.1).map (wordField u p.2))
    (fun p => (a p.1).map (wordField u (i::p.2)) + (a (i::p.1)).map (wordField u p.2)) (by
      intro p hp
      have hlen := derivativeSplits_lengths l p hp
      exact (wordField_weak u p.2 i (by omega)).mul hS hν (a p.1) (a (i::p.1))
        (ha p.1) (hd p.1 i))
  change IsWeakSpatialDerivative ν S _ (leibnizField a u l) _ at hh
  convert hh using 1
  simp only [leibnizField, derivativeSplits, List.map_append, List.map_map, List.sum_append,
    List.sum_map_add]
  exact add_comm _ _

/-- If the original A2-preserved state belongs to H^n, every actual derivative
is the proved Leibniz expansion; no derivative formula is taken as input. -/
theorem wordField_mul (a : List (Fin d) → BoundedMultiplier ν)
    (ha : ∀ l, ContDiffOn ℝ ∞ (a l).value S)
    (hd : ∀ l i, (a (i::l)).value =ᵐ[ν]
      (fun x => fderiv ℝ (a l).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u v : WeakSobolevJet d n ν S) (hv : value v = (a []).map (value u))
    (l : List (Fin d)) (hl : l.length ≤ n) : wordField v l = leibnizField a u l := by
  induction l with
  | nil => simpa only [wordField_nil, leibnizField_nil] using hv
  | cons i l ih =>
    have hlen : l.length < n := by simp only [List.length_cons] at hl; omega
    have he := ih (by omega)
    have hw := wordField_weak v l i hlen
    rw [he] at hw
    exact hw.unique hS hν (leibnizField_weak hS hν a ha hd u l i hlen)
end WeakSobolevJet
end Carleman
