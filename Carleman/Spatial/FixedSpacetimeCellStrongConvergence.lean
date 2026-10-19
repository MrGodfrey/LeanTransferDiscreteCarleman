module

public import Carleman.Spatial.FixedSpacetimeCellReconstruction
public import Carleman.Spatial.FiniteCellStrongConvergence

/-! Actual spacetime averages converge in L² under independent space and time refinement. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 1200000 in
theorem fixedSpacetimeCell_average_strong_convergence (T : ℝ) (hTpos : 0 ≤ T) (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (u : Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    Tendsto (fun n => fixedSpacetimeCellIsometry T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n)
      ((fixedSpacetimeCellIsometry T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n)).toContinuousLinearMap.adjoint u))
      atTop (𝓝 u) := by
  let μ := (volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))
  let K n := cartesianSpacetimeCell lo (δ n) (N n) (g n)
  let mass n := (g n).dt*(∏ j, δ n j)
  have hm n : 0 < mass n := mul_pos (g n).dt_pos (Finset.prod_pos (fun j _ => hδ n j))
  have hvol n a : μ.real (K n a)=mass n := by
    have he := cartesianSpacetimeCell_restrict_volume lo (δ n) (hδ n) (N n) (g n) a
    rw [hT n,funext (hbox n)] at he
    exact he
  let A := Icc 0 T ×ˢ closure (openCoordinateBox lo hi)
  have hA : IsCompact A := isCompact_Icc.prod (openCoordinateBox_isBounded lo hi).isCompact_closure
  let p (n : ℕ) (a : Fin (g n).steps × CartesianInteriorIndex (N n)) :=
    ((g n).nodeTime a.1,cartesianInteriorPoint lo (δ n) (N n) a.2)
  have hp n a : p n a ∈ A := by
    constructor
    · have he := (g n).physicalTimeCell_subset a.1
        (show (g n).nodeTime a.1+(g n).dt ∈ (g n).physicalTimeCell a.1 from
          ⟨by linarith [(g n).dt_pos],le_rfl⟩)
      rw [hT n] at he
      exact ⟨(g n).nodeTime_nonneg a.1,by linarith [(g n).dt_pos,he.2]⟩
    · apply subset_closure
      have he := cartesianInteriorPoint_mem lo (δ n) (hδ n) (N n) a.2
      rw [funext (hbox n)] at he
      exact he
  have hinc n a : K n a ⊆ A := by
    intro x hx
    constructor
    · have ht := (g n).physicalTimeCell_subset a.1 hx.1
      rw [hT n] at ht
      exact ⟨ht.1.le,ht.2⟩
    · apply subset_closure
      have hs := cartesianDualCell_subset lo (δ n) (hδ n) (N n) a.2 hx.2
      rw [funext (hbox n)] at hs
      exact hs
  let r n := (g n).dt+(d:ℝ)*h n
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa using htlim.add ((tendsto_const_nhds (x := (d:ℝ))).mul hlim)
  have hdist n a x (hx : x ∈ K n a) : dist x (p n a) ≤ r n := by
    rw [Prod.dist_eq]
    apply max_le
    · have ht := hx.1
      change (g n).nodeTime a.1 < x.1 ∧ x.1 ≤ (g n).nodeTime a.1+(g n).dt at ht
      change dist x.1 ((g n).nodeTime a.1) ≤ (g n).dt+(d:ℝ)*h n
      rw [Real.dist_eq,abs_of_nonneg (by linarith [ht.1])]
      nlinarith [mul_nonneg (Nat.cast_nonneg d : (0:ℝ)≤d) (hh n)]
    · change dist x.2 (cartesianInteriorPoint lo (δ n) (N n) a.2) ≤ (g n).dt+(d:ℝ)*h n
      have hd := cartesianDualCell_dist_le lo (δ n) (hδ n) (N n) (hh n) (hstep n) a.2 hx.2
      linarith [(g n).dt_pos]
  have hδlim j : Tendsto (fun n => δ n j) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hδ n j).le) (fun n => hstep n j) hlim
  have hstrip := fixedSpacetime_uncovered_volume_tendsto T hTpos lo hi δ hδ N hN hbox g hT hδlim
  exact finiteCell_average_strong_convergence K (fun n => cartesianSpacetimeCell_measurable lo (δ n) (N n) (g n))
    mass hm (fun n => cartesianSpacetimeCell_disjoint lo (δ n) (hδ n) (N n) (g n)) hvol
    A hA p hp hinc r hr hdist hstrip u

end Carleman
