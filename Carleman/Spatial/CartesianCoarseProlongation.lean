module

public import Carleman.Spatial.TensorProlongationInverse
public import Carleman.Spatial.CartesianBoxValues
public import Carleman.Spatial.CartesianPhysicalStiffness

/-! Actual tensor prolongation into the original fine physical Hilbert space,
and its precise mass and stiffness identities. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianCoarseProlongation (h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) : (CartesianInteriorIndex K → ℝ) →ₗ[ℝ]
      CartesianPhysicalState h hh (fun r => m r*K r) where
  toFun u := PhysicalFiniteSpace.valuesEquiv.symm
    (fun a => tensorLinearProlongation m K u (fun r => (a r).val+1))
  map_add' := by
    intro u v
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    change (∑ b, (u b+v b)*_)=(∑ b, u b*_)+(∑ b, v b*_)
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro c u
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    change (∑ b, (c*u b)*_)=c*(∑ b, u b*_)
    simp only [mul_assoc,Finset.mul_sum]

theorem cartesianCoarseProlongation_values (h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (u : CartesianInteriorIndex K → ℝ)
    (a : CartesianInteriorIndex (fun r => m r*K r)) :
    cartesianCoarseProlongation h hh m K u a=
      tensorLinearProlongation m K u (fun r => (a r).val+1) := rfl

theorem cartesianCoarseProlongation_mass (h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ) :
    ‖cartesianCoarseProlongation h hh m K u‖^2 =
      (∏ r, h r)*∑ z : ∀ r, Fin (m r*K r),
        (tensorLinearProlongation m K u (fun r => (z r).val))^2 := by
  rw [PhysicalFiniteSpace.norm_sq,cartesian_sum_box_values _
    (fun z => (tensorLinearProlongation m K u z)^2) (by
      intro z r hr
      rw [tensorLinearProlongation_zero_face m K hm u z r (Or.inl hr)]
      norm_num)]
  rfl

theorem cartesianCoarseProlongation_axis (o h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ)
    (z : ∀ r, Fin (m r*K r)) (r : Fin d) :
    cartesianAxisDifference o h (fun j => m j*K j)
      (fun a => cartesianCoarseProlongation h hh m K u a) (fun j => ((z j).val:ℤ)) r =
      (tensorLinearProlongation m K u (Function.update (fun j => (z j).val) r ((z r).val+1))-
        tensorLinearProlongation m K u (fun j => (z j).val))/h r := by
  classical
  have hV := tensorLinearProlongation_zero_face m K hm u
  have hb : ∀ j, (z j).val ≤ m j*K j := fun j => (z j).isLt.le
  have hs : ∀ j, Function.update (fun j => (z j).val) r ((z r).val+1) j ≤ m j*K j := by
    intro j
    by_cases hj : j=r
    · subst j; simp only [Function.update_self]; exact (z r).isLt
    · rw [Function.update_of_ne hj]; exact hb j
  change (cartesianLatticeData o h _ (fun a => tensorLinearProlongation m K u (fun j => (a j).val+1))
    (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r)-
    cartesianLatticeData o h _ (fun a => tensorLinearProlongation m K u (fun j => (a j).val+1))
      (fun j => ((z j).val:ℤ)))/h r=_
  rw [cartesianLatticeSuccessor_nat,
    cartesianLatticeData_of_box_values o h hh _ _ hV _ hs,
    cartesianLatticeData_of_box_values o h hh _ _ hV _ hb]

theorem cartesianCoarseProlongation_energy (o h : Fin d → ℝ) (hh : ∀ r, 0 < h r)
    (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r) (u : CartesianInteriorIndex K → ℝ) :
    inner ℝ (cartesianPhysicalLaplacian o h hh (fun r => m r*K r)
      (cartesianCoarseProlongation h hh m K u)) (cartesianCoarseProlongation h hh m K u) =
      (∏ r, h r)*∑ z : ∀ r, Fin (m r*K r), ∑ r : Fin d,
        ((tensorLinearProlongation m K u (Function.update (fun j => (z j).val) r ((z r).val+1))-
          tensorLinearProlongation m K u (fun j => (z j).val))/h r)^2 := by
  rw [cartesianPhysicalState_inner]
  change cartesianPhysicalInner h (fun r => m r*K r)
    (cartesianFiniteDifferenceLaplacian o h (fun r => m r*K r)
      (fun a => cartesianCoarseProlongation h hh m K u a))
    (fun a => cartesianCoarseProlongation h hh m K u a)=_
  rw [cartesianFiniteDifferenceLaplacian_pairing_edges o h hh]
  simp_rw [cartesianCoarseProlongation_axis o h hh m K hm,← pow_two]

end Carleman
