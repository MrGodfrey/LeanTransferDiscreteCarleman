module

public import Carleman.Control.CartesianSpacetimePotential
public import Carleman.Spatial.FixedBoxCellReconstruction

/-! Actual spacetime cell reconstruction and uncovered measure in one fixed spacetime domain. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman
variable {d : ℕ}

def fixedSpacetimeCellIsometry (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T) :
    PhysicalFiniteSpace (Fin g.steps × CartesianInteriorIndex N) (g.dt*(∏ j, δ j))
      (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j))) →ₗᵢ[ℝ]
      Lp ℝ 2 ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))) :=
  finiteCellIsometry (cartesianSpacetimeCell lo δ N g) (cartesianSpacetimeCell_measurable lo δ N g)
    (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j))) (cartesianSpacetimeCell_disjoint lo δ hδ N g)
    (by intro a; have he := cartesianSpacetimeCell_restrict_volume lo δ hδ N g a
        rw [hT,funext hbox] at he; exact he)

theorem fixedSpacetime_uncovered_volume (T : ℝ) (hTpos : 0 ≤ T)
    (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T) :
    ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))).real
      (⋃ a : Fin g.steps × CartesianInteriorIndex N, cartesianSpacetimeCell lo δ N g a)ᶜ=
      T*(volume.restrict (openCoordinateBox lo hi)).real
        (⋃ a : CartesianInteriorIndex N, cartesianDualCell lo δ N a)ᶜ := by
  let ν := volume.restrict (openCoordinateBox lo hi)
  let μ := (volume.restrict (Ioc 0 T)).prod ν
  have ht : (volume.restrict (Ioc 0 T)).real univ=T := by
    simp only [Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real,Real.volume_real_Ioc_of_le hTpos,sub_zero]
  have hfull : μ.real univ=T*ν.real univ := by
    rw [show (univ : Set (ℝ × SpatialCoordinates d))=(univ : Set ℝ) ×ˢ univ from (univ_prod_univ).symm,
      measureReal_prod_prod,ht]
  have hv a : ν.real (cartesianDualCell lo δ N a)=∏ j, δ j := by
    have he := cartesianDualCell_restrict_volume lo δ hδ N a
    rw [funext hbox] at he
    exact he
  have htv a : μ.real (cartesianSpacetimeCell lo δ N g a)=g.dt*(∏ j, δ j) := by
    have he := cartesianSpacetimeCell_restrict_volume lo δ hδ N g a
    rw [hT,funext hbox] at he
    exact he
  have hunion : μ.real (⋃ a : Fin g.steps × CartesianInteriorIndex N, cartesianSpacetimeCell lo δ N g a)=
      T*ν.real (⋃ a : CartesianInteriorIndex N, cartesianDualCell lo δ N a) := by
    rw [finiteCells_union_volume _ (cartesianSpacetimeCell_measurable lo δ N g)
      (cartesianSpacetimeCell_disjoint lo δ hδ N g) htv,
      finiteCells_union_volume _ (cartesianDualCell_measurable lo δ N)
        (cartesianDualCell_disjoint lo δ hδ N) hv]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    have hp : (g.steps:ℝ)*g.dt=T := hT
    rw [← hp]
    ring
  change μ.real _=T*ν.real _
  rw [measureReal_compl (MeasurableSet.iUnion (cartesianSpacetimeCell_measurable lo δ N g)),
    measureReal_compl (MeasurableSet.iUnion (cartesianDualCell_measurable lo δ N)),hfull,hunion]
  ring

theorem fixedSpacetime_uncovered_volume_tendsto (T : ℝ) (hTpos : 0 ≤ T) (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (hlim : ∀ j, Tendsto (fun n => δ n j) atTop (𝓝 0)) :
    Tendsto (fun n => ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))).real
      (⋃ a : Fin (g n).steps × CartesianInteriorIndex (N n), cartesianSpacetimeCell lo (δ n) (N n) (g n) a)ᶜ)
      atTop (𝓝 0) := by
  have he n := fixedSpacetime_uncovered_volume T hTpos lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n)
  simp_rw [he]
  simpa using (tendsto_const_nhds (x := T)).mul
    (cartesianBox_uncovered_volume_tendsto lo hi δ hδ N hN hbox hlim)

end Carleman
