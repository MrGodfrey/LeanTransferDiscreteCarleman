module

public import Carleman.Spatial.ContractedNodalSobolev
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete inward sequence and actual derivative convergence on locally
affine pieces; the simplicial interfaces have zero Lebesgue measure. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace Carleman
variable {d : ℕ}

def inwardRatio (n : ℕ) : ℝ := (1+(n:ℝ))/(2+(n:ℝ))

theorem inwardRatio_pos (n : ℕ) : 0 < inwardRatio n := by
  unfold inwardRatio
  positivity

theorem inwardRatio_lt_one (n : ℕ) : inwardRatio n < 1 := by
  unfold inwardRatio
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem inwardRatio_half_le (n : ℕ) : (1:ℝ)/2 ≤ inwardRatio n := by
  unfold inwardRatio
  apply (le_div_iff₀ (by positivity)).mpr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem inwardRatio_inv_le_two (n : ℕ) : (inwardRatio n)⁻¹ ≤ 2 := by
  apply (inv_le_iff_one_le_mul₀ (inwardRatio_pos n)).mpr
  linarith [inwardRatio_half_le n]

theorem inwardRatio_tendsto : Tendsto inwardRatio atTop (𝓝 (1:ℝ)) := by
  change Tendsto (fun n : ℕ => (1+(n:ℝ))/(2+(n:ℝ))) atTop (𝓝 (1:ℝ))
  simpa only [one_mul,div_one] using tendsto_add_mul_div_add_mul_atTop_nhds (1:ℝ) 2 1
    (d := 1) (by norm_num)

theorem inverse_inward_tendsto (a x : SpatialCoordinates d) :
    Tendsto (fun n => (centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').symm x)
      atTop (𝓝 x) := by
  have hr : Tendsto (fun n => (inwardRatio n)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa using inwardRatio_tendsto.inv₀ (by norm_num)
  have hh := (tendsto_const_nhds (x := a)).add
    (hr.smul (tendsto_const_nhds (x := x-a)))
  simpa [centeredDilation] using hh

theorem inwardFunction_tendsto (a : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} (hf : Continuous f) (x : SpatialCoordinates d) :
    Tendsto (fun n => contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' f x)
      atTop (𝓝 (f x)) := hf.continuousAt.tendsto.comp (inverse_inward_tendsto a x)

theorem inward_fderiv_tendsto_of_local_affine (a x : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} {A : SpatialCoordinates d →L[ℝ] ℝ}
    (hA : ∀ᶠ y in 𝓝 x, HasFDerivAt f A y) :
    Tendsto (fun n => fderiv ℝ
      (contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' f) x)
      atTop (𝓝 (fderiv ℝ f x)) := by
  have hx : fderiv ℝ f x = A := (mem_of_mem_nhds hA).fderiv
  rw [hx]
  have he : ∀ᶠ n in atTop, fderiv ℝ
      (contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' f) x =
      (inwardRatio n)⁻¹ • A := by
    filter_upwards [(inverse_inward_tendsto a x).eventually hA] with n hn
    rw [(contractedFunction_hasFDerivAt a _ _ hn).fderiv]
    ext y
    simp
  have hr : Tendsto (fun n => (inwardRatio n)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa using inwardRatio_tendsto.inv₀ (by norm_num)
  simpa only [one_smul] using (hr.smul (tendsto_const_nhds (x := A))).congr' (he.mono fun _ hn => hn.symm)

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

theorem nodal_inward_fderiv_tendsto_ae (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) (a : SpatialCoordinates d) :
    ∀ᵐ x ∂volume, Tendsto (fun n => fderiv ℝ
      (contractedFunction a (inwardRatio n) (inwardRatio_pos n).ne' (M.nodalFunction f)) x)
      atTop (𝓝 (fderiv ℝ (M.nodalFunction f) x)) := by
  have hn (i : ι) : ∀ᵐ x ∂volume, x ∉ frontier (M.cell i) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using simplicialCell_frontier_null (M.simplex i).points
  filter_upwards [ae_all_iff.mpr hn] with x hfront
  by_cases hc : x ∈ closure S
  · rw [← M.cells_union] at hc
    obtain ⟨i,hi⟩ := mem_iUnion.mp hc
    have hint := (mem_interior_iff_notMem_frontier hi).mpr (hfront i)
    apply inward_fderiv_tendsto_of_local_affine a x (A := M.localNodalDerivative f i)
    filter_upwards [isOpen_interior.mem_nhds hint] with y hy
    exact M.nodalFunction_hasFDerivAt_on_interior hM f i hy
  · apply inward_fderiv_tendsto_of_local_affine a x (A := 0)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    apply (hasFDerivAt_const (0:ℝ) y).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
    exact M.nodalFunction_zero_outside f hz

end SimplicialPartition
end Carleman
