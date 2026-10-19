module

public import Carleman.Geometry.EuclideanCoordinateSplit
public import Mathlib.Tactic.Module

/-! Actual linear coordinates whose vertical unit direction is a prescribed
nonzero Euclidean vector. No orthogonality is needed for Lipschitz charts. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ}

def shearDirectionCoordinates (v : SpatialCoordinates d) (s : ℝ) (hs : s ≠ 0) :
    (SpatialCoordinates d × ℝ) ≃L[ℝ] SpatialCoordinates d × ℝ :=
  (show (SpatialCoordinates d × ℝ) ≃ₗ[ℝ] SpatialCoordinates d × ℝ from
    { toFun := fun p => (p.1-(p.2/s) • v,p.2/s)
      invFun := fun p => (p.1+p.2 • v,s*p.2)
      left_inv := fun p => by
        apply Prod.ext
        · exact sub_add_cancel _ _
        · change s*(p.2/s)=p.2
          field_simp
      right_inv := fun p => by
        apply Prod.ext <;> simp [hs]
      map_add' := fun p q => by
        apply Prod.ext
        · simp only [Prod.fst_add,Prod.snd_add,add_div,add_smul]
          abel
        · exact add_div _ _ _
      map_smul' := fun c p => by
        apply Prod.ext
        · change c • p.1-((c*p.2)/s) • v=c • (p.1-(p.2/s) • v)
          rw [mul_div_assoc,smul_sub,mul_smul]
        · change (c*p.2)/s=c*(p.2/s)
          exact mul_div_assoc _ _ _ }).toContinuousLinearEquiv

theorem shearDirectionCoordinates_direction (v : SpatialCoordinates d) (s : ℝ) (hs : s ≠ 0) :
    shearDirectionCoordinates v s hs (v,s)=(0,1) := by
  change (v-(s/s) • v,s/s)=(0,1)
  simp [hs]

theorem exists_directional_coordinates (v : SpatialCoordinates (d+1)) (hv : v ≠ 0) :
    ∃ e : SpatialCoordinates (d+1) ≃L[ℝ] SpatialCoordinates d × ℝ, e v=(0,1) := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    apply hv
    exact PiLp.ext h
  obtain ⟨i,hi⟩ := hex
  refine ⟨(coordinateSplit i).trans
    (shearDirectionCoordinates (WithLp.toLp 2 (fun j => v (i.succAbove j))) (v i) hi),?_⟩
  exact shearDirectionCoordinates_direction _ _ hi

end Carleman
