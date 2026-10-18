module

public import Carleman.Geometry.ClosedCoordinateFaces
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! The actual coordinate box is convex and has positive finite volume when
all side lengths are positive. The unit cube has a dimension-only diameter bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem openCoordinateBox_convex (a b : Fin d → ℝ) : Convex ℝ (openCoordinateBox a b) := by
  have he : openCoordinateBox a b = ⋂ j, (EuclideanSpace.proj j) ⁻¹' Ioo (a j) (b j) := by
    ext x
    simp only [openCoordinateBox,mem_ofPred_eq,mem_iInter,mem_preimage,mem_Ioo]
    rfl
  rw [he]
  exact convex_iInter fun j => (convex_Ioo (a j) (b j)).linear_preimage (EuclideanSpace.proj j).toLinearMap

theorem openCoordinateBox_nonempty (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j) :
    (openCoordinateBox a b).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun j => (a j+b j)/2),?_⟩
  intro j
  change a j < (a j+b j)/2 ∧ (a j+b j)/2 < b j
  constructor <;> linarith [hpos j]

theorem openCoordinateBox_volume_pos (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j) :
    0 < volume.real (openCoordinateBox a b) :=
  ENNReal.toReal_pos ((openCoordinateBox_isOpen a b).measure_pos volume
    (openCoordinateBox_nonempty a b hpos)).ne'
    (openCoordinateBox_isBounded a b).measure_lt_top.ne

theorem unitCube_diameter_bound (x y : SpatialCoordinates d)
    (hx : x ∈ openCoordinateBox (fun _ => 0) (fun _ => 1))
    (hy : y ∈ openCoordinateBox (fun _ => 0) (fun _ => 1)) : dist x y ≤ (d : ℝ) := by
  have hs : ‖x-y‖^2 ≤ (d:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        change (x i-y i)^2 ≤ 1
        have h1 : 0 ≤ 1-(x i-y i) := by linarith [(hx i).1,(hx i).2,(hy i).1,(hy i).2]
        have h2 : 0 ≤ 1+(x i-y i) := by linarith [(hx i).1,(hx i).2,(hy i).1,(hy i).2]
        nlinarith [mul_nonneg h1 h2]
      _ = _ := by simp
  have hnat : (d:ℝ) ≤ (d:ℝ)^2 := by
    simpa only [pow_two] using (show (d:ℝ) ≤ (d:ℝ)*(d:ℝ) by exact_mod_cast Nat.le_mul_self d)
  rw [dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg d)).mp (hs.trans hnat)

end Carleman
