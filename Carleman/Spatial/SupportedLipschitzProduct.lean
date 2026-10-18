module

public import Carleman.Spatial.SimplicialNodalLipschitz
public import Carleman.Weights.SquaredWithinDerivatives
public import Carleman.Weights.SpatialComparison

/-! A bounded coefficient on the support suffices for a genuine global
Lipschitz product; no regularity outside the support is assumed. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem supported_lipschitz_product {K : Set (SpatialCoordinates d)}
    (w u : SpatialCoordinates d → ℝ) (B P L D : ℝ≥0)
    (hu : LipschitzWith L u) (hw : LipschitzOnWith D w K)
    (hB : ∀ x ∈ K, |w x| ≤ B) (hP : ∀ x, |u x| ≤ P)
    (hzero : ∀ x ∉ K, u x=0) :
    LipschitzWith (B*L+P*D) (fun x => w x*u x) := by
  have hcross {x y : SpatialCoordinates d} (hx : x ∈ K) (hy : y ∉ K) :
      |w x*u x-w y*u y| ≤ (B*L+P*D:ℝ≥0)*dist x y := by
    have hl : |u x| ≤ L*dist x y := by
      have hh := hu.dist_le_mul x y
      simpa only [Real.dist_eq,hzero y hy,sub_zero] using hh
    rw [hzero y hy,mul_zero,sub_zero,abs_mul]
    calc
      _ ≤ (B:ℝ)*(L*dist x y) := mul_le_mul (hB x hx) hl (abs_nonneg _) B.property
      _ ≤ (B*L+P*D:ℝ≥0)*dist x y := by
        simp only [NNReal.coe_add,NNReal.coe_mul]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg P.property D.property)) dist_nonneg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hl : |u x-u y| ≤ L*dist x y := by simpa only [Real.dist_eq] using hu.dist_le_mul x y
      have hd : |w x-w y| ≤ D*dist x y := by simpa only [Real.dist_eq] using hw.dist_le_mul x hx y hy
      calc
        _ = |w x*(u x-u y)+(w x-w y)*u y| := by congr 1; ring
        _ ≤ |w x| *|u x-u y|+|w x-w y| *|u y| := by simpa only [abs_mul] using abs_add_le (w x*(u x-u y)) ((w x-w y)*u y)
        _ ≤ (B:ℝ)*(L*dist x y)+(D*dist x y)*P :=
          add_le_add (mul_le_mul (hB x hx) hl (abs_nonneg _) B.property)
            (mul_le_mul hd (hP y) (abs_nonneg _) (by positivity))
        _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul]; ring
    · exact hcross hx hy
  · by_cases hy : y ∈ K
    · simpa only [abs_sub_comm,dist_comm] using hcross hy hx
    · rw [hzero x hx,hzero y hy,mul_zero,mul_zero,sub_self,abs_zero]
      positivity

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

theorem squared_nodal_product_lipschitz (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    {ρ : SpatialCoordinates d → ℝ} (hρ : ContDiffOn ℝ 2 ρ (closure S))
    (q τ η : ℝ) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => allowedSquaredWeight ρ q τ η x*M.nodalFunction f x) := by
  let w := allowedSquaredWeight ρ q τ η
  have hw := allowedSquaredWeight_contDiffOn hρ q τ η
  obtain ⟨D,hD,hLip⟩ := smooth_profile_lipschitz hS hc hcompact (hw.of_le (by norm_num))
  obtain ⟨B,hbound⟩ := hcompact.exists_bound_of_continuousOn hw.continuousOn
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  let P : ℝ≥0 := ⟨M.nodalBound f,M.nodalBound_nonneg f⟩
  let D' : ℝ≥0 := ⟨D,zero_le_one.trans hD⟩
  have hwLip : LipschitzOnWith D' w (closure S) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact hLip x hx y hy
  refine ⟨B'*M.nodalLipschitzConstant f+P*D',?_⟩
  apply supported_lipschitz_product w (M.nodalFunction f) B' P _ D'
    (M.nodalFunction_lipschitzWith hS hM hB f hf) hwLip
  · intro x hx
    exact (show |w x| ≤ B by simpa only [Real.norm_eq_abs] using hbound x hx).trans (le_max_left _ _)
  · exact M.nodalFunction_bound hM f
  · exact fun _ hx => M.nodalFunction_zero_outside f hx

end SimplicialPartition
end Carleman
