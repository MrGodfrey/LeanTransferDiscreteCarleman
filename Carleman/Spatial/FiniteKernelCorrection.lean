module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Correct a finite-dimensional vector into the kernel of an actual linear
map, with a bound by its image. A finite family admits one uniform constant. -/
@[expose] public noncomputable section
namespace Carleman
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem finiteDimensional_kernel_correction (L : V →ₗ[ℝ] W) :
    ∃ C > 0, ∀ p : V, ∃ q : V, L q=0 ∧ ‖p-q‖ ≤ C*‖L p‖ := by
  let f : V →L[ℝ] L.range := L.rangeRestrict.toContinuousLinearMap
  have hsurj : Function.Surjective f := by
    rintro ⟨y,x,hx⟩
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨C,hC,hpre⟩ := f.exists_preimage_norm_le hsurj
  refine ⟨C,hC,?_⟩
  intro p
  obtain ⟨r,hr,hn⟩ := hpre (f p)
  have he : L r=L p := congrArg Subtype.val hr
  refine ⟨p-r,?_,?_⟩
  · rw [map_sub,he,sub_self]
  · change ‖r‖ ≤ C*‖L p‖ at hn
    simpa only [sub_sub_cancel] using hn

theorem finiteFamily_kernel_correction {ι : Type*} [Fintype ι] (L : ι → V →ₗ[ℝ] W) :
    ∃ C > 0, ∀ j : ι, ∀ p : V, ∃ q : V, L j q=0 ∧ ‖p-q‖ ≤ C*‖L j p‖ := by
  classical
  choose c hc hcorr using fun j => finiteDimensional_kernel_correction (L j)
  have hsum : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => (hc j).le
  refine ⟨1+∑ j, c j,by linarith,?_⟩
  intro j p
  obtain ⟨q,hq,hbound⟩ := hcorr j p
  refine ⟨q,hq,hbound.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  have hj : c j ≤ ∑ k, c k := Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ j)
  linarith

end Carleman
