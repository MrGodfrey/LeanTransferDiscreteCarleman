module

public import Carleman.Spatial.CartesianObservationLocalization

/-! The actual observation nodes, zero extension and restriction, with the
paper's physical pairing and weighted observation norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

abbrev CartesianObservationIndex (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) :=
  {a : CartesianInteriorIndex N // cartesianInteriorPoint o δ N a ∈ ω}

def cartesianControlRestriction (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) :
    (CartesianInteriorIndex N → ℝ) →ₗ[ℝ] (CartesianObservationIndex o δ N ω → ℝ) where
  toFun := fun f a => f a.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def cartesianControlExtension (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) :
    (CartesianObservationIndex o δ N ω → ℝ) →ₗ[ℝ] (CartesianInteriorIndex N → ℝ) where
  toFun := fun v a => if ha : cartesianInteriorPoint o δ N a ∈ ω then v ⟨a,ha⟩ else 0
  map_add' := by
    intro f g
    funext a
    by_cases ha : cartesianInteriorPoint o δ N a ∈ ω <;> simp [ha]
  map_smul' := by
    intro c f
    funext a
    by_cases ha : cartesianInteriorPoint o δ N a ∈ ω <;> simp [ha]

def cartesianControlPhysicalInner (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d))
    (v z : CartesianObservationIndex o δ N ω → ℝ) : ℝ := by
  classical
  exact (∏ j, δ j)*∑ a : CartesianObservationIndex o δ N ω, v a*z a

def cartesianControlWeightedSq (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (v : CartesianObservationIndex o δ N ω → ℝ) : ℝ := by
  classical
  exact (∏ j, δ j)*∑ a : CartesianObservationIndex o δ N ω,
    (σ (cartesianInteriorPoint o δ N a.val)*v a)^2

theorem cartesianControlRestriction_extension (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (v : CartesianObservationIndex o δ N ω → ℝ) :
    cartesianControlRestriction o δ N ω (cartesianControlExtension o δ N ω v)=v := by
  funext a
  change (if ha : cartesianInteriorPoint o δ N a.val ∈ ω then v ⟨a.val,ha⟩ else 0)=v a
  simp only [dite_eq_left a.property]

theorem cartesianControlExtension_restriction (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (f : CartesianInteriorIndex N → ℝ) :
    cartesianControlExtension o δ N ω (cartesianControlRestriction o δ N ω f)=
      cartesianObservedState o δ N ω f := by
  funext a
  rw [cartesianObservedState_apply]
  change (if ha : cartesianInteriorPoint o δ N a ∈ ω then f a else 0)=_
  rfl

theorem cartesianControlExtension_pairing (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (v : CartesianObservationIndex o δ N ω → ℝ)
    (f : CartesianInteriorIndex N → ℝ) :
    cartesianPhysicalInner δ N (cartesianControlExtension o δ N ω v) f=
      cartesianControlPhysicalInner o δ N ω v (cartesianControlRestriction o δ N ω f) := by
  classical
  unfold cartesianPhysicalInner cartesianControlPhysicalInner
  congr 1
  let A := Finset.univ.filter (fun a : CartesianInteriorIndex N => cartesianInteriorPoint o δ N a ∈ ω)
  calc
    _ = ∑ a ∈ A, (cartesianControlExtension o δ N ω v) a*f a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ hn
      have ha : cartesianInteriorPoint o δ N a ∉ ω := by simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using hn
      simp [cartesianControlExtension,ha]
    _ = ∑ a : CartesianObservationIndex o δ N ω,
        (cartesianControlExtension o δ N ω v) a.val*f a.val :=
      Finset.sum_subtype A (by simp [A]) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp [cartesianControlExtension,cartesianControlRestriction,a.property]

theorem cartesianObservedState_weighted_energy (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (f : CartesianInteriorIndex N → ℝ) :
    cartesianWeightedNodeEnergy o δ N σ (cartesianObservedState o δ N ω f)=
      cartesianControlWeightedSq o δ N ω σ (cartesianControlRestriction o δ N ω f) := by
  classical
  unfold cartesianWeightedNodeEnergy cartesianControlWeightedSq
  congr 1
  simp only [cartesianObservedState_apply]
  simp only [mul_ite,mul_zero,ite_pow,zero_pow (by decide : 2 ≠ 0),← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end Carleman
