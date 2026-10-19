module

public import Carleman.Spatial.FiniteOddBoxExtension
public import Carleman.Spatial.EvenLocalMollification

/-! The actual mollifications of the full Poisson extension vanish on every box face. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Convolution ContDiff
namespace Carleman
variable {d : ℕ}

theorem IsOddInSlab.even_mollification_zero
    {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {r : Fin d} {c δ : ℝ} (h : IsOddInSlab u r c δ) (n : ℕ)
    (hn : (shrinkingBump d n).rOut ≤ δ) {x : SpatialCoordinates d} (hx : x r=c) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value) x=0 := by
  rw [real_convolution_comm]
  apply evenSpatialMollifier_convolution_zero n r c hx
  filter_upwards [h] with y hy
  intro hym
  apply hy
  have hc : |y r-c| ≤ dist y x := by
    rw [dist_eq_norm,← hx]
    exact PiLp.norm_apply_le (y-x) r
  exact hc.trans_lt ((Metric.mem_ball.mp hym).trans_le hn)

theorem frontier_box_has_coordinate_face (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    {x : SpatialCoordinates d} (hx : x ∈ frontier (openCoordinateBox a b)) :
    ∃ r, x r=a r ∨ x r=b r := by
  have hc : x ∈ closedCoordinateBox a b := by
    rw [← closure_openCoordinateBox a b hpos]; exact hx.1
  have hn : ¬ ∀ r, a r < x r ∧ x r < b r := by
    intro h; exact hx.2 ((openCoordinateBox_isOpen a b).interior_eq.symm ▸ h)
  obtain ⟨r,hr⟩ := not_forall.mp hn
  refine ⟨r,?_⟩
  by_cases he : x r=a r
  · exact Or.inl he
  · right
    have hlt : a r < x r := lt_of_le_of_ne (hc r).1 (Ne.symm he)
    exact le_antisymm (hc r).2 (not_lt.mp (fun h => hr ⟨hlt,h⟩))

theorem even_mollification_eventually_zero_boundary (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (ho : ∀ r, IsOddInSlab u r (a r) (b r-a r) ∧ IsOddInSlab u r (b r) (b r-a r)) :
    ∀ᶠ n in atTop, ∀ x ∈ frontier (openCoordinateBox a b),
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value) x=0 := by
  have hs : ∀ᶠ n in atTop, ∀ r, (shrinkingBump d n).rOut < b r-a r :=
    eventually_all.mpr fun r => shrinkingBump_rOut_tendsto.eventually
      (gt_mem_nhds (sub_pos.mpr (hpos r)))
  filter_upwards [hs] with n hn
  intro x hx
  obtain ⟨r,hr⟩ := frontier_box_has_coordinate_face a b hpos hx
  rcases hr with hr | hr
  · exact (ho r).1.even_mollification_zero n (hn r).le hr
  · exact (ho r).2.even_mollification_zero n (hn r).le hr

theorem exists_box_poisson_extension_smooth_boundary (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f) :
    ∃ v g, IsPoissonExtension (expandedBox_contains a b Finset.univ) ((4:ℝ)^d) u f v g ∧
      let V := zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet (WeakSobolevJet.value v)
      (∀ n, ContDiff ℝ ∞
        (V ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value)) ∧
      (∀ᶠ n in atTop, ∀ x ∈ frontier (openCoordinateBox a b),
        (V ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (evenSpatialMollifier d n).value) x=0) := by
  obtain ⟨v,g,hv,ho⟩ := exists_finite_odd_box_extension a b hpos Finset.univ u hu f hf
  simp only [Finset.card_univ,Fintype.card_fin] at hv
  refine ⟨v,g,hv,fun n => (evenSpatialMollifier d n).smooth_convolution _,?_⟩
  exact even_mollification_eventually_zero_boundary a b hpos _ (fun r => ho r (Finset.mem_univ r))

end Carleman
