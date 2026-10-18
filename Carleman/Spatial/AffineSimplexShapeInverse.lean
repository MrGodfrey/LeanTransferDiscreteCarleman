module

public import Carleman.Spatial.AffineSimplexInverse

/-! An actual contained ball controls the inverse coordinate map.
Thus bounded diameter/inradius ratio supplies the uniform local inverse bound. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem affineSimplex_inverse_map_bound (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ simplicialCell T.points, ‖x‖ ≤ R)
    (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b a : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball a r ⊆ simplicialCell (affineSimplex T A b).points) :
    ‖A.symm.toContinuousLinearMap‖ ≤ 4*R/r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  have ha := hball (Metric.mem_ball_self hr)
  have hy : a+(r/2) • x ∈ simplicialCell (affineSimplex T A b).points := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr),hx,mul_one]
    linarith
  rw [affineSimplex_cell] at ha hy
  obtain ⟨u,hu,hua⟩ := ha
  obtain ⟨v,hv,hva⟩ := hy
  have hd : A (v-u) = (r/2) • x := by
    calc
      _ = affineChange A b v-affineChange A b u := by simp only [affineChange_apply,map_sub,add_sub_add_right_eq_sub]
      _ = (r/2) • x := by rw [hva,hua]; abel
  have hd' : v-u = (r/2) • A.symm x := by
    apply A.injective
    rw [hd,map_smul,ContinuousLinearEquiv.apply_symm_apply]
  have hn : ‖v-u‖ ≤ 2*R := (norm_sub_le v u).trans (by linarith [hbound v hv,hbound u hu])
  rw [hd',norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr)] at hn
  change ‖A.symm x‖ ≤ 4*R/r
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hn]

theorem affineSimplex_shape_inverse (κ : ℝ) (hκ : 0 < κ) : ∃ C > (0:ℝ),
    ∀ (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b a : SpatialCoordinates d)
      (r h : ℝ), 0 < r → 0 < h →
      Metric.ball a r ⊆ simplicialCell (affineSimplex T A b).points → h ≤ κ*r →
    ∀ c : Fin (d+1) → ℝ,
    ‖simplexNodalGradientLp (affineSimplex T A b) c‖ ≤
      (C/h)*‖simplexNodalLp (affineSimplex T A b) c‖ := by
  obtain ⟨R,hR,hbound⟩ := (simplicialCell_compact T.points).isBounded.exists_pos_norm_le
  obtain ⟨C,hC,hcb⟩ := affineSimplex_inverse_uniform T (4*R*κ) (by positivity)
  refine ⟨C,hC,?_⟩
  intro A b a r h hr hh hball hshape c
  apply hcb A b h hh _ c
  calc
    _ ≤ 4*R/r := affineSimplex_inverse_map_bound T R hR.le hbound A b a r hr hball
    _ ≤ (4*R*κ)/h := by
      apply (div_le_div_iff₀ hr hh).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hshape (by positivity : 0 ≤ 4*R)]

end Carleman
