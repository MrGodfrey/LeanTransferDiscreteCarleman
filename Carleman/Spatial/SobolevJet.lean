module

public import Carleman.Spatial.WeakDerivative
public import Carleman.Spatial.ExpressionTimeNorm
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Concrete finite Sobolev jets of L² fields

A multi-index is a multiset of coordinate directions (`Sym`); mixed derivative
permutations therefore represent one component, not repeated copies. Each
order has the Euclidean norm on all its components, exactly the manuscript's
D^k convention. Weak derivatives are distributional, via `SpatialTest`.
This constructs the spatial data; identifying an existing abstract V with this
space and proving evolution regularity are separate remaining obligations.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

abbrev SpatialCoordinates (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev DerivativeFiber (d k : ℕ) := EuclideanSpace ℝ (Sym (Fin d) k)
abbrev JetFields (d m : ℕ) (ν : Measure (SpatialCoordinates d)) :=
  ∀ k : Fin (m+1), Lp (DerivativeFiber d k.val) 2 ν

/-- Extracting a component from an L² vector field is a genuine bounded linear map. -/
def derivativeComponent {d k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) : Lp (DerivativeFiber d k) 2 ν →ₗ[ℝ] Lp ℝ 2 ν :=
  (OperatorMultiplier.const (EuclideanSpace.proj α)).linearMap

theorem derivativeComponent_ae {d k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) :
    derivativeComponent α u =ᵐ[ν] (fun x => u x α) :=
  OperatorMultiplier.const_map_ae (EuclideanSpace.proj α) u

/-- All orders up to m linked by the actual weak derivative identity. -/
def weakJetSubmodule (d m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (S : Set (SpatialCoordinates d)) :
    Submodule ℝ (JetFields d m ν) where
  carrier := {u | ∀ (k : Fin m) (α : Sym (Fin d) k.val) (i : Fin d),
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (derivativeComponent α (u k.castSucc))
      (derivativeComponent (Sym.cons i α) (u k.succ))}
  zero_mem' := by
    intro k α i
    simp only [Pi.zero_apply, map_zero]
    exact IsWeakSpatialDerivative.zero
  add_mem' := by
    intro u v hu hv k α i
    simp only [Pi.add_apply, map_add]
    exact (hu k α i).add (hv k α i)
  smul_mem' := by
    intro c u hu k α i
    simp only [Pi.smul_apply, map_smul]
    exact (hu k α i).smul c

abbrev WeakSobolevJet (d m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (S : Set (SpatialCoordinates d)) :=
  weakJetSubmodule d m ν S

namespace WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

/-- The actual k-th derivative collection, as a linear L² field of the jet. -/
def field (k : Fin (m+1)) : WeakSobolevJet d m ν S →ₗ[ℝ] Lp (DerivativeFiber d k.val) 2 ν :=
  (LinearMap.proj k).comp (weakJetSubmodule d m ν S).subtype

theorem field_weak_derivative (u : WeakSobolevJet d m ν S) (k : Fin m)
    (α : Sym (Fin d) k.val) (i : Fin d) :
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (derivativeComponent α (field k.castSucc u))
      (derivativeComponent (Sym.cons i α) (field k.succ u)) := u.property k α i

/-- The spatial graph term is the L² norm of the full Euclidean derivative
collection; all components occur once, including mixed multi-indices. -/
theorem field_weighted_sq (w : BoundedMultiplier ν) (k : Fin (m+1))
    (u : WeakSobolevJet d m ν S) :
    (w.seminorm (field k u))^2 =
      ∫ x, |w.value x|^2 * ∑ α : Sym (Fin d) k.val, (field k u x α)^2 ∂ν := by
  rw [w.seminorm_sq_integral]
  simp only [EuclideanSpace.real_norm_sq_eq]

/-- An expression with ordinary bounded scalar coefficients on this genuine
Sobolev jet. Its order is structural and its field is an actual L² element. -/
def expression {j : ℕ}
    (c : ∀ k : Fin (m+1), Sym (Fin d) k.val → BoundedMultiplier ν) :
    DifferentialExpression ν (fun k : Fin (m+1) => DerivativeFiber d k.val) ℝ j where
  coefficient k := OperatorMultiplier.ofCoefficients (c k)

/-- The already proved order bound specializes to the genuine weak jet fields. -/
theorem expression_weighted_density_le {j : ℕ}
    (c : ∀ k : Fin (m+1), Sym (Fin d) k.val → BoundedMultiplier ν)
    (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S)
    {q a b : ℝ} (hq : 1 ≤ q)
    (hexp : ∀ k : Fin (m+1), k.val ≤ j → a ≤ 2*(m-k.val : ℕ)+b) :
    q^a * (w.seminorm ((expression (j := j) c).onFields field u))^2 ≤
      (expression (j := j) c).boundSq * ∑ k : Fin (m+1),
        q^(2*(m-k.val : ℕ)+b) * (w.seminorm (field k u))^2 :=
  (expression c).weighted_density_le w (fun k => field k u) hq hexp

/-- The same genuine weak jets admit vector-valued differential expressions,
including the gradient; each coefficient is an ordinary bounded vector field. -/
def vectorExpression {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}
    (c : ∀ k : Fin (m+1), Sym (Fin d) k.val → VectorCoefficient ν F) :
    DifferentialExpression ν (fun k : Fin (m+1) => DerivativeFiber d k.val) F j where
  coefficient k := OperatorMultiplier.ofVectorCoefficients (c k)

theorem vectorExpression_apply_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}
    (c : ∀ k : Fin (m+1), Sym (Fin d) k.val → VectorCoefficient ν F)
    (u : WeakSobolevJet d m ν S) :
    (vectorExpression (j := j) c).onFields field u =ᵐ[ν]
      (fun x => ∑ k ∈ (Finset.univ.filter (fun k : Fin (m+1) => k.val ≤ j)),
        ∑ α : Sym (Fin d) k.val, field k u x α • (c k α).value x) := by
  change (vectorExpression (j := j) c).apply (fun k => field k u) =ᵐ[ν] _
  simpa only [DifferentialExpression.orders, vectorExpression, OperatorMultiplier.ofVectorCoefficients_apply]
    using (vectorExpression (j := j) c).apply_ae (fun k => field k u)

end WeakSobolevJet
end Carleman
