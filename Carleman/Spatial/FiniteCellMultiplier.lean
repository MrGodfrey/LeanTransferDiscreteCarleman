module

public import Carleman.Spatial.FiniteCellReconstruction
public import Carleman.Spatial.PhysicalFiniteWeights

/-! The actual cellwise potential and its exact physical multiplication and pairing. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {Ω ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν] [Fintype ι]
  (K : ι → Set Ω) (hK : ∀ i, MeasurableSet (K i))
attribute [local instance] Classical.propDecidable

def finiteCellFunction (c : ι → ℝ) (x : Ω) : ℝ := ∑ i, (K i).indicator (fun _ => c i) x

omit [MeasurableSpace Ω] in
theorem finiteCellFunction_on_cell (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (c : ι → ℝ) (i : ι) {x : Ω} (hx : x ∈ K i) : finiteCellFunction K c x=c i := by
  rw [finiteCellFunction,Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (hdis hji) hj hx) _
  · simp

omit [MeasurableSpace Ω] in
theorem finiteCellFunction_zero_outside (c : ι → ℝ) {x : Ω} (hx : x ∉ ⋃ i, K i) :
    finiteCellFunction K c x=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩)) _

omit [MeasurableSpace Ω] in
theorem finiteCellFunction_bound (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (c : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B) (x : Ω) :
    |finiteCellFunction K c x| ≤ B := by
  by_cases hx : x ∈ ⋃ i, K i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [finiteCellFunction_on_cell K hdis c i hi]
    exact hc i
  · rw [finiteCellFunction_zero_outside K c hx,abs_zero]
    exact hB

def finiteCellMultiplier (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (c : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B) : BoundedMultiplier ν where
  value := finiteCellFunction K c
  measurable := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact aestronglyMeasurable_const.indicator (hK i)
  bound := B
  bound_nonneg := hB
  bounded := Filter.Eventually.of_forall (finiteCellFunction_bound K hdis c hB hc)

theorem finiteCellMultiplier_commute (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (c : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B)
    {mass : ℝ} (hm : 0 < mass) (f : PhysicalFiniteSpace ι mass hm) :
    (finiteCellMultiplier K hK hdis c B hB hc).map (finiteCellLinear (ν := ν) K hK hm f)=
      finiteCellLinear (ν := ν) K hK hm (PhysicalFiniteSpace.multiplier c f) := by
  apply Lp.ext
  filter_upwards [(finiteCellMultiplier K hK hdis c B hB hc).map_ae (finiteCellLinear (ν := ν) K hK hm f),
    finiteCellLinear_ae (ν := ν) K hK hm f,
    finiteCellLinear_ae (ν := ν) K hK hm (PhysicalFiniteSpace.multiplier c f)] with x hb hx hprod
  rw [hb,hx,hprod]
  change finiteCellFunction K c x*finiteCellFunction K f x=
    finiteCellFunction K (PhysicalFiniteSpace.multiplier c f) x
  by_cases hi : x ∈ ⋃ i, K i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hi
    rw [finiteCellFunction_on_cell K hdis c i hi,finiteCellFunction_on_cell K hdis f i hi,
      finiteCellFunction_on_cell K hdis (PhysicalFiniteSpace.multiplier c f) i hi]
    rfl
  · rw [finiteCellFunction_zero_outside K c hi,finiteCellFunction_zero_outside K (PhysicalFiniteSpace.multiplier c f) hi,zero_mul]

theorem finiteCellMultiplier_pairing (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (c : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B)
    {mass : ℝ} (hm : 0 < mass) (hvol : ∀ i, ν.real (K i)=mass)
    (f z : PhysicalFiniteSpace ι mass hm) :
    inner ℝ ((finiteCellMultiplier K hK hdis c B hB hc).map (finiteCellIsometry K hK hm hdis hvol f))
      (finiteCellIsometry K hK hm hdis hvol z)=inner ℝ (PhysicalFiniteSpace.multiplier c f) z := by
  change inner ℝ ((finiteCellMultiplier K hK hdis c B hB hc).map (finiteCellLinear K hK hm f))
    (finiteCellLinear K hK hm z)=_
  rw [finiteCellMultiplier_commute,finiteCellLinear_inner K hK hm hdis hvol]

end Carleman
