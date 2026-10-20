module

public import Carleman.Control.BochnerProductL2
public import Carleman.Spatial.FixedSpacetimeCellReconstruction

/-! The original finite-difference spacetime cells and average potentials under the actual L² isometry. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators Topology
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesian_time_product_reconstruction
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
    (u : Fin g.steps → CartesianPhysicalState δ hδ N) :
    bochnerL2ProductIsometry (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (u i)))=
      cartesianSpacetimeCellIsometry o δ hδ N g
        (PhysicalFiniteSpace.valuesEquiv.symm (fun a => u a.1 a.2)) := by
  apply Lp.ext
  have he : ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      ∀ i : Fin g.steps, cartesianCellIsometry o δ hδ N (u i) x=
        ∑ a, (cartesianDualCell o δ N a).indicator (fun _ => u i a) x := by
    apply Filter.eventually_all.mpr
    intro i
    exact cartesianCellIsometry_ae o δ hδ N (u i)
  filter_upwards [bochnerL2ProductIsometry_time_ae g (fun i => cartesianCellIsometry o δ hδ N (u i)),
    finiteCellLinear_ae (cartesianSpacetimeCell o δ N g) (cartesianSpacetimeCell_measurable o δ N g)
      (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j)))
      (PhysicalFiniteSpace.valuesEquiv.symm (fun a => u a.1 a.2)),
    quasiMeasurePreserving_snd.ae he] with z hz hp hez
  change _=(finiteCellLinear _ _ _ _) z
  rw [hp,hz,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hti : z.1∈g.physicalTimeCell i
  · rw [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' g.physicalTimeCell i from hti),hez i]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hxa : z.2∈cartesianDualCell o δ N a <;>
      simp [cartesianSpacetimeCell,hti,hxa,PhysicalFiniteSpace.valuesEquiv]; rfl
  · simp [cartesianSpacetimeCell,hti]

theorem cartesian_time_product_potential
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (u : Fin g.steps → CartesianPhysicalState δ hδ N) :
    bochnerL2ProductIsometry (timeCellReconstruction g (fun i =>
      (cartesianReconstructedPotential o δ hδ N g b i).map (cartesianCellIsometry o δ hδ N (u i))))=
      (cartesianSpacetimePotential o δ hδ N g b).map
        (bochnerL2ProductIsometry (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (u i)))) := by
  simp_rw [cartesianReconstructedPotential_commute]
  rw [cartesian_time_product_reconstruction,cartesian_time_product_reconstruction]
  have hp := finiteCellMultiplier_commute (mass := g.dt*(∏ j, δ j))
    (ν := (volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (cartesianSpacetimeCell o δ N g)
    (cartesianSpacetimeCell_measurable o δ N g) (cartesianSpacetimeCell_disjoint o δ hδ N g)
    (fun a => cartesianAveragedPotential o δ N g b a.1 a.2)
    b.bound b.bound_nonneg (fun a => cartesianAveragedPotential_bound o δ hδ N g b a.1 a.2)
    (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j)))
    (PhysicalFiniteSpace.valuesEquiv.symm (fun a => u a.1 a.2))
  exact hp.symm


theorem cartesian_fixed_time_product_reconstruction
    (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (u : Fin g.steps → CartesianPhysicalState δ hδ N) :
    bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
      (fun i => cartesianBoxCellIsometry lo hi δ hδ N hbox (u i)))=
      fixedSpacetimeCellIsometry T lo hi δ hδ N hbox g hT
        (PhysicalFiniteSpace.valuesEquiv.symm (fun a => u a.1 a.2)) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesian_time_product_reconstruction lo δ hδ N g u

theorem cartesian_time_product_potential_pairing
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (u v : Fin g.steps → CartesianPhysicalState δ hδ N) :
    inner ℝ (timeCellReconstruction g (fun i =>
      (cartesianReconstructedPotential o δ hδ N g b i).map (cartesianCellIsometry o δ hδ N (u i))))
      (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (v i)))=
      inner ℝ ((cartesianSpacetimePotential o δ hδ N g b).map
        (bochnerL2ProductIsometry (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (u i)))))
        (bochnerL2ProductIsometry (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (v i)))) := by
  rw [← cartesian_time_product_potential]
  exact (bochnerL2ProductIsometry.inner_map_map _ _).symm

end Carleman
