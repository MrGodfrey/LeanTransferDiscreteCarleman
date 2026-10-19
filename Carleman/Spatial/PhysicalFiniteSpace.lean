module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A finite physical Hilbert space with its actual positive mass weight.
The separate type keeps its physical norm distinct from the function sup norm. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

def PhysicalFiniteSpace (ι : Type*) (mass : ℝ) (_hmass : 0 < mass) := ι → ℝ

namespace PhysicalFiniteSpace
variable {ι : Type*} {mass : ℝ} {hmass : 0 < mass}

instance : CoeFun (PhysicalFiniteSpace ι mass hmass) (fun _ => ι → ℝ) := ⟨fun f => f⟩
instance : AddCommGroup (PhysicalFiniteSpace ι mass hmass) := inferInstanceAs (AddCommGroup (ι → ℝ))
instance : Module ℝ (PhysicalFiniteSpace ι mass hmass) := inferInstanceAs (Module ℝ (ι → ℝ))

def valuesEquiv : PhysicalFiniteSpace ι mass hmass ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.refl ℝ _

variable [Fintype ι]

@[instance_reducible] def core : InnerProductSpace.Core ℝ (PhysicalFiniteSpace ι mass hmass) where
  inner f g := mass*∑ i, f i*g i
  conj_inner_symm := by intro f g; simp only [conj_trivial,mul_comm]
  re_inner_nonneg f := mul_nonneg hmass.le (Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i)))
  add_left := by
    intro f g z
    change mass*(∑ i, (f i+g i)*z i)=mass*(∑ i, f i*z i)+mass*(∑ i, g i*z i)
    simp only [add_mul,Finset.sum_add_distrib,mul_add]
  smul_left := by
    intro f g c
    change mass*(∑ i, (c*f i)*g i)=c*(mass*∑ i, f i*g i)
    simp only [mul_assoc,← Finset.mul_sum]
    ring
  definite := by
    intro f hf
    have hs : ∑ i, (f i)^2=0 := by
      have hz := (mul_eq_zero.mp hf).resolve_left hmass.ne'
      simpa only [pow_two] using hz
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).mp hs
    funext i
    exact sq_eq_zero_iff.mp (hi i (Finset.mem_univ i))

instance : NormedAddCommGroup (PhysicalFiniteSpace ι mass hmass) :=
  letI := core (ι := ι) (hmass := hmass)
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ (PhysicalFiniteSpace ι mass hmass) :=
  InnerProductSpace.ofCore (core (ι := ι) (hmass := hmass)).toCore

instance : FiniteDimensional ℝ (PhysicalFiniteSpace ι mass hmass) :=
  FiniteDimensional.of_injective (valuesEquiv (ι := ι) (hmass := hmass)).toLinearMap
    (valuesEquiv (ι := ι) (hmass := hmass)).injective

instance : CompleteSpace (PhysicalFiniteSpace ι mass hmass) := FiniteDimensional.complete ℝ _

theorem inner_eq (f g : PhysicalFiniteSpace ι mass hmass) :
    inner ℝ f g=mass*∑ i, f i*g i := rfl

theorem norm_sq (f : PhysicalFiniteSpace ι mass hmass) :
    ‖f‖^2=mass*∑ i, (f i)^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_eq]
  simp only [pow_two]

theorem norm_eq (f : PhysicalFiniteSpace ι mass hmass) :
    ‖f‖=Real.sqrt (mass*∑ i, (f i)^2) := by
  rw [← norm_sq,Real.sqrt_sq (norm_nonneg f)]

def multiplier (b : ι → ℝ) : PhysicalFiniteSpace ι mass hmass →L[ℝ] PhysicalFiniteSpace ι mass hmass :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f i => b i*f i
    map_add' := by intro f g; funext i; exact mul_add _ _ _
    map_smul' := by intro c f; funext i; change _*(c*_)=c*(_*_); ring }

theorem multiplier_apply (b : ι → ℝ) (f : PhysicalFiniteSpace ι mass hmass) (i : ι) :
    multiplier b f i=b i*f i := rfl

theorem multiplier_norm_sq (b : ι → ℝ) (f : PhysicalFiniteSpace ι mass hmass) :
    ‖multiplier b f‖^2=mass*∑ i, (b i*f i)^2 := norm_sq _

end PhysicalFiniteSpace
end Carleman
