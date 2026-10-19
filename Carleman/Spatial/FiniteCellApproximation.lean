module

public import Carleman.Spatial.FiniteCellReconstruction
public import Carleman.Spatial.IsometricReconstructionProjection
public import Mathlib.MeasureTheory.Measure.Real

/-! A genuine L² cell approximation estimate retaining the uncovered boundary region. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {Ω ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν] [Fintype ι]
  (K : ι → Set Ω) (hK : ∀ i, MeasurableSet (K i)) {mass : ℝ} (hm : 0 < mass)
attribute [local instance] Classical.propDecidable

include hK in
theorem finiteCells_union_volume (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i) = mass) : ν.real (⋃ i, K i) = (Fintype.card ι : ℝ)*mass := by
  rw [measureReal_iUnion_fintype hdis hK]
  simp only [hvol,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem finiteCellLinear_error_bound (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (f : PhysicalFiniteSpace ι mass hm) (u : Lp ℝ 2 ν) {ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hloc : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → |u x-f i| ≤ ε)
    (hbound : ∀ᵐ x ∂ν, |u x| ≤ B) :
    ‖u-finiteCellLinear K hK hm f‖^2 ≤ ε^2*ν.real univ+B^2*ν.real (⋃ i, K i)ᶜ := by
  let A := ⋃ i, K i
  have hA : MeasurableSet A := MeasurableSet.iUnion hK
  let w := u-finiteCellLinear K hK hm f
  let q : Ω → ℝ := A.indicator (fun _ => ε^2)+Aᶜ.indicator (fun _ => B^2)
  have hq : Integrable q ν :=
    ((integrable_const (ε^2)).indicator hA).add ((integrable_const (B^2)).indicator hA.compl)
  have hw : Integrable (fun x => ‖w x‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)
  have hpoint : ∀ᵐ x ∂ν, ‖w x‖^2 ≤ q x := by
    filter_upwards [Lp.coeFn_sub u (finiteCellLinear K hK hm f),finiteCellLinear_ae K hK hm f,
      ae_all_iff.mpr hloc,hbound] with x hwx hEx hlocal hbx
    change ‖((u-finiteCellLinear (ν := ν) K hK hm f : Lp ℝ 2 ν) : Ω → ℝ) x‖^2 ≤ q x
    rw [hwx]
    simp only [Pi.sub_apply,hEx]
    by_cases hx : x ∈ A
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      have hs : (∑ j, (K j).indicator (fun _ => f j) x) = f i := by
        rw [Finset.sum_eq_single i]
        · exact Set.indicator_of_mem hi _
        · intro j _ hji
          exact Set.indicator_of_notMem (fun hj => Set.disjoint_left.mp (hdis hji) hj hi) _
        · simp
      rw [hs]
      have hb := (sq_le_sq₀ (abs_nonneg _) hε).mpr (hlocal i hi)
      simpa only [q,Pi.add_apply,indicator_of_mem hx,indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx),
        add_zero,Real.norm_eq_abs] using hb
    · have hs : (∑ j, (K j).indicator (fun _ => f j) x) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact Set.indicator_of_notMem (fun hj => hx (mem_iUnion.mpr ⟨j,hj⟩)) _
      rw [hs,sub_zero]
      have hb := (sq_le_sq₀ (abs_nonneg _) hB).mpr hbx
      simpa only [q,Pi.add_apply,indicator_of_notMem hx,indicator_of_mem (show x ∈ Aᶜ from hx),
        zero_add,Real.norm_eq_abs] using hb
  have hn : ‖w‖^2 = ∫ x, ‖w x‖^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hqi : (∫ x, q x ∂ν) = ε^2*ν.real A+B^2*ν.real Aᶜ := by
    dsimp only [q, Pi.add_apply]
    rw [integral_add ((integrable_const (ε^2)).indicator hA) ((integrable_const (B^2)).indicator hA.compl),
      integral_indicator hA,integral_indicator hA.compl]
    simp only [setIntegral_const,smul_eq_mul]
    ring
  calc
    ‖w‖^2 = ∫ x, ‖w x‖^2 ∂ν := hn
    _ ≤ ∫ x, q x ∂ν := integral_mono_ae hw hq hpoint
    _ = ε^2*ν.real A+B^2*ν.real Aᶜ := hqi
    _ ≤ ε^2*ν.real univ+B^2*ν.real Aᶜ :=
      add_le_add (mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) (subset_univ A)) (sq_nonneg ε)) le_rfl

theorem finiteCell_average_error_bound (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i) = mass) (f : PhysicalFiniteSpace ι mass hm) (u : Lp ℝ 2 ν)
    {ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hloc : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → |u x-f i| ≤ ε)
    (hbound : ∀ᵐ x ∂ν, |u x| ≤ B) :
    ‖u-finiteCellIsometry K hK hm hdis hvol
      ((finiteCellIsometry K hK hm hdis hvol).toContinuousLinearMap.adjoint u)‖^2 ≤
      ε^2*ν.real univ+B^2*ν.real (⋃ i, K i)ᶜ := by
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (reconstruction_best_approximation (finiteCellIsometry K hK hm hdis hvol) u f) 2).trans
  exact finiteCellLinear_error_bound K hK hm hdis f u hε hB hloc hbound

end Carleman
