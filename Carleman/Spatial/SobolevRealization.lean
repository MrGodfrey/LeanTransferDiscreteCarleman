module

public import Carleman.Spatial.SobolevJet
public import Carleman.Spatial.WeakDerivativeUnique

/-! Identification of a concrete Sobolev jet with its zeroth L² component.
The derivative data are unique on an open spatial domain. This gives a genuine
linear subspace of H=L², with canonical linear derivative fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

/-- Equality of every scalar component determines the whole L² vector class. -/
theorem derivativeComponent_ext {d k : ℕ} {ν : Measure (SpatialCoordinates d)}
    {u v : Lp (DerivativeFiber d k) 2 ν}
    (h : ∀ α, derivativeComponent α u = derivativeComponent α v) : u = v := by
  have ha : ∀ α, (fun x => u x α) =ᵐ[ν] (fun x => v x α) := by
    intro α
    exact (derivativeComponent_ae α u).symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 ν => (z : _ → ℝ)) (h α))).trans
        (derivativeComponent_ae α v))
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr ha] with x hx
  ext α
  exact hx α

/-- The empty multi-index has exactly one Euclidean component. -/
theorem derivativeFiber_zero_norm_sq {d : ℕ} (v : DerivativeFiber d 0) :
    ‖v‖^2 = (v Sym.nil)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_unique _

namespace WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)}

/-- The zeroth field is one scalar component (the empty multi-index). -/
def value : WeakSobolevJet d m ν S →ₗ[ℝ] Lp ℝ 2 ν :=
  (derivativeComponent Sym.nil).comp (field 0)

theorem eq_zero_of_value_eq_zero (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (u : WeakSobolevJet d m ν S) (hu : value u = 0) : u = 0 := by
  have hz : ∀ k : ℕ, ∀ hk : k ≤ m, field (⟨k, by omega⟩ : Fin (m+1)) u = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      apply derivativeComponent_ext
      intro α
      rw [Sym.eq_nil_of_card_zero α, map_zero]
      exact hu
    | succ k ih =>
      intro hk
      apply derivativeComponent_ext
      intro α
      obtain ⟨i, α, rfl⟩ := Sym.exists_eq_cons_of_succ α
      have hw := u.property (⟨k, by omega⟩ : Fin m) α i
      change IsWeakSpatialDerivative ν S _
        (derivativeComponent α (field (⟨k, by omega⟩ : Fin (m+1)) u)) _ at hw
      rw [ih (by omega), map_zero] at hw
      exact (hw.of_zero hS hν).trans (map_zero _).symm
  apply Subtype.ext
  funext k
  exact hz k.val (by omega)

theorem value_injective (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S) :
    Function.Injective (value (d := d) (m := m) (ν := ν) (S := S)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply eq_zero_of_value_eq_zero hS hν
  rw [map_sub, huv, sub_self]

end WeakSobolevJet

/-- A concrete H^m subspace of the actual scalar L² space. -/
def sobolevSubspace (d m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (S : Set (SpatialCoordinates d)) : Submodule ℝ (Lp ℝ 2 ν) :=
  LinearMap.range (WeakSobolevJet.value (d := d) (m := m) (ν := ν) (S := S))

/-- Recover the unique genuine weak derivative jet of a member of H^m. -/
def sobolevJetEquiv {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S) :
    WeakSobolevJet d m ν S ≃ₗ[ℝ] sobolevSubspace d m ν S :=
  LinearEquiv.ofInjective _ (WeakSobolevJet.value_injective hS hν)

/-- Canonical L² derivative fields on the H-subspace, no arbitrary named maps. -/
def sobolevDerivative {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (k : Fin (m+1)) : sobolevSubspace d m ν S →ₗ[ℝ] Lp (DerivativeFiber d k.val) 2 ν :=
  (WeakSobolevJet.field k).comp (sobolevJetEquiv hS hν).symm.toLinearMap

theorem sobolevDerivative_weak {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (u : sobolevSubspace d m ν S) (k : Fin m) (α : Sym (Fin d) k.val) (i : Fin d) :
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (derivativeComponent α (sobolevDerivative hS hν k.castSucc u))
      (derivativeComponent (Sym.cons i α) (sobolevDerivative hS hν k.succ u)) :=
  WeakSobolevJet.field_weak_derivative ((sobolevJetEquiv hS hν).symm u) k α i

/-- The recovered empty multi-index is exactly the original H-valued class. -/
theorem sobolevDerivative_zero_value {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (u : sobolevSubspace d m ν S) :
    derivativeComponent Sym.nil (sobolevDerivative hS hν 0 u) = (u : Lp ℝ 2 ν) :=
  LinearEquiv.ofInjective_symm_apply _ (h := WeakSobolevJet.value_injective hS hν) u

/-- Exact equality of the zeroth weighted gradient norm with the state's
actual scalar L² norm; no equivalence constant or new assumption. -/
theorem sobolevDerivative_zero_seminorm {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (u : sobolevSubspace d m ν S) :
    w.seminorm (sobolevDerivative hS hν 0 u) = w.seminorm (u : Lp ℝ 2 ν) := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [w.seminorm_sq_integral, w.seminorm_sq_integral]
  apply integral_congr_ae
  have hz := derivativeComponent_ae Sym.nil (sobolevDerivative hS hν 0 u)
  rw [sobolevDerivative_zero_value] at hz
  filter_upwards [hz] with x hx
  have hn : ‖sobolevDerivative hS hν 0 u x‖^2 =
      (sobolevDerivative hS hν 0 u x Sym.nil)^2 :=
    derivativeFiber_zero_norm_sq (sobolevDerivative hS hν 0 u x)
  apply congrArg (fun y : ℝ => |w.value x|^2 * y)
  calc
    _ = _ := hn
    _ = ((u : Lp ℝ 2 ν) x)^2 := congrArg (fun y : ℝ => y^2) hx.symm
    _ = _ := by rw [Real.norm_eq_abs, sq_abs]
end Carleman
