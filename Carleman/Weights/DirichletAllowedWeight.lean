module

public import Carleman.Spatial.DirichletWeakProduct
public import Carleman.Weights.SpatialComparison

/-! The original smooth-on-closure allowed weights preserve the full H¹₀
space. No exterior smooth extension or nodal representation is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem allowed_multiplier_boundedSmooth (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) :
    BoundedSmoothOn ((ρ.scaled η).multiplier w τ t).value S := by
  have hb := (hρ.boundedSmoothOn hbounded).allowedWeight hS (w.lower t) τ η hη
  have he : ((ρ.scaled η).multiplier w τ t).value =
      (fun x => (w.q t)^τ*Real.exp (w.q t*(η*ρ.value x))) := by
    funext x
    change (w.q t)^τ*Real.exp ((η*ρ.value x)*w.q t) = _
    rw [mul_comm (η*ρ.value x) (w.q t)]
  rw [he]
  exact hb

theorem allowed_weight_mem_dirichlet (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1)
    (u : Lp ℝ 2 (volume.restrict S)) (hu : u ∈ dirichletSubspace S) :
    ((ρ.scaled η).multiplier w τ t).map u ∈ dirichletSubspace S :=
  boundedSmooth_map_mem_dirichlet hS _ (allowed_multiplier_boundedSmooth hS hbounded ρ hρ w τ t η hη) u hu

theorem allowed_squared_residual_mem_dirichlet (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1)
    (u I : Lp ℝ 2 (volume.restrict S)) (hu : u ∈ dirichletSubspace S) (hI : I ∈ dirichletSubspace S)
    (e : WeakSobolevJet d 1 (volume.restrict S) S)
    (he : WeakSobolevJet.value e=
      (((ρ.scaled η).multiplier w τ t).mul ((ρ.scaled η).multiplier w τ t)).map u-I) :
    e ∈ dirichletJetSpace S := by
  apply (mem_dirichletJetSpace_iff S hS e).mpr
  rw [he,BoundedMultiplier.mul_map]
  exact (dirichletSubspace S).sub_mem
    (allowed_weight_mem_dirichlet hS hbounded ρ hρ w τ t η hη _
      (allowed_weight_mem_dirichlet hS hbounded ρ hρ w τ t η hη u hu)) hI

end Carleman
