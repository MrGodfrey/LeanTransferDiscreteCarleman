module

public import Carleman.Spatial.BoundedSecondMoment

/-! Exact second moments of genuine simplex barycentric coordinates. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem integral_unit_tail_power (d : ℕ) :
    (∫ t in Ioc (0:ℝ) 1, t*(1-t)^d) = 1/((d+1:ℝ)*(d+2)) := by
  have hi (n : ℕ) : IntervalIntegrable (fun t : ℝ => (1-t)^n) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (1-t)^n)).intervalIntegrable 0 1
  have hp (n : ℕ) : (∫ t in (0:ℝ)..1, (1-t)^n) = 1/(n+1:ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
    norm_num only [sub_self,sub_zero]
    rw [integral_pow]
    simp only [one_pow,zero_pow (Nat.succ_ne_zero n),sub_zero]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have he : (fun t : ℝ => t*(1-t)^d) = fun t => (1-t)^d-(1-t)^(d+1) := by
    funext t
    rw [pow_succ]
    ring
  rw [he,intervalIntegral.integral_sub (hi d) (hi (d+1)),hp,hp]
  push_cast
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  field_simp
  ring

theorem integral_simplexBarycentric_sq {d : ℕ}
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (i : Fin (d+1)) :
    (∫ x in simplicialCell T.points, (simplexBarycentric T i x)^2) =
      2*volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2)) := by
  have hm := (simplexBarycentric T i).continuous_of_finiteDimensional.measurable
  have hn : 0 ≤ᵐ[volume.restrict (simplicialCell T.points)] simplexBarycentric T i := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    exact simplexBarycentric_nonneg T hx i
  have hb : simplexBarycentric T i ≤ᵐ[volume.restrict (simplicialCell T.points)] (fun _ => 1) := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    exact simplexBarycentric_le_one T i hx
  rw [integral_sq_eq_tail _ hm.aemeasurable hn hb]
  have he : (∫ t in Ioc (0:ℝ) 1, t *
      (volume.restrict (simplicialCell T.points)).real {x | t ≤ simplexBarycentric T i x}) =
      (∫ t in Ioc (0:ℝ) 1, t*(1-t)^d)*volume.real (simplicialCell T.points) := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne (volume : Measure ℝ) 1).filter_mono ae_restrict_le] with t ht hne
    rw [simplexBarycentric_superlevel_real T i ht.1.le (lt_of_le_of_ne ht.2 hne)]
    ring
  rw [he,integral_unit_tail_power]
  ring

end Carleman
