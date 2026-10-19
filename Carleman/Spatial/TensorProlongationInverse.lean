module

public import Carleman.Spatial.TensorLinearProlongation
public import Carleman.Geometry.CartesianAxisSum

/-! The original coefficient twelve for the tensor prolongation, with the
actual fine nodal mass and coordinate difference quotients. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem tensorLinearProlongation_line_inverse (m K : Fin d → ℕ)
    (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ) (r : Fin d)
    (w : ∀ j : {j // j ≠ r}, Fin (m j*K j)) {h : ℝ} (hh : 0 < h) :
    (∑ k ∈ Finset.range (m r*K r),
      ((tensorLinearProlongation m K u (cartesianAxisFill (fun j => m j*K j) r w (k+1))-
        tensorLinearProlongation m K u (cartesianAxisFill (fun j => m j*K j) r w k))/h)^2) ≤
      12/((m r:ℝ)*h)^2*(∑ k ∈ Finset.range (m r*K r),
        (tensorLinearProlongation m K u (cartesianAxisFill (fun j => m j*K j) r w k))^2) := by
  let v : ℕ → ℝ := fun n => tensorLinearProlongation m K u
    (cartesianAxisFill (fun j => m j*K j) r w (m r*n))
  have he (k : ℕ) : tensorLinearProlongation m K u
      (cartesianAxisFill (fun j => m j*K j) r w k)=uniformLinearProlongation (m r) v k := by
    simpa only [cartesianAxisFill_update] using
      tensorLinearProlongation_slice m K hm u (cartesianAxisFill (fun j => m j*K j) r w 0) r k
  have h0 : v 0=0 := tensorLinearProlongation_zero_face m K hm u _ r
    (Or.inl (by simp [cartesianAxisFill]))
  have hK : v (K r)=0 := tensorLinearProlongation_zero_face m K hm u _ r
    (Or.inr (cartesianAxisFill_self _ _ _ _))
  simp_rw [he]
  apply (mul_le_mul_iff_right₀ hh).mp
  simpa only [mul_left_comm] using
    uniformLinearProlongation_physical_inverse (m r) (K r) (hm r) v h0 hK hh

theorem tensorLinearProlongation_direction_inverse (m K : Fin d → ℕ)
    (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ) (r : Fin d)
    {h : ℝ} (hh : 0 < h) :
    (∑ z : ∀ j, Fin (m j*K j),
      ((tensorLinearProlongation m K u (Function.update (fun j => (z j).val) r ((z r).val+1))-
        tensorLinearProlongation m K u (fun j => (z j).val))/h)^2) ≤
      12/((m r:ℝ)*h)^2*(∑ z : ∀ j, Fin (m j*K j),
        (tensorLinearProlongation m K u (fun j => (z j).val))^2) := by
  classical
  rw [cartesian_sum_axis _ r (fun z =>
    ((tensorLinearProlongation m K u (Function.update z r (z r+1))-
      tensorLinearProlongation m K u z)/h)^2),
    cartesian_sum_axis _ r (fun z => (tensorLinearProlongation m K u z)^2),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  simpa only [cartesianAxisFill_self,cartesianAxisFill_update] using
    tensorLinearProlongation_line_inverse m K hm u r w hh

theorem tensorLinearProlongation_inverse (m K : Fin d → ℕ)
    (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ)
    (h : Fin d → ℝ) (hh : ∀ r, 0 < h r) :
    (∑ z : ∀ j, Fin (m j*K j), ∑ r : Fin d,
      ((tensorLinearProlongation m K u (Function.update (fun j => (z j).val) r ((z r).val+1))-
        tensorLinearProlongation m K u (fun j => (z j).val))/h r)^2) ≤
      (∑ r, 12/((m r:ℝ)*h r)^2)*(∑ z : ∀ j, Fin (m j*K j),
        (tensorLinearProlongation m K u (fun j => (z j).val))^2) := by
  rw [Finset.sum_comm,Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ => tensorLinearProlongation_direction_inverse m K hm u r (hh r)

end Carleman
