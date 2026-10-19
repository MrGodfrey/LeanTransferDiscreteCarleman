module

public import Carleman.Spatial.FixedSpacetimeCellStrongConvergence

/-! The original a.e. bounded potential, its true averaged reconstruction, and strong L² consistency. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman
namespace BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

def toL2 (b : BoundedMultiplier ν) : Lp ℝ 2 ν :=
  (MemLp.of_bound b.measurable b.bound (by simpa only [Real.norm_eq_abs] using b.bounded)).toLp b.value

theorem toL2_ae (b : BoundedMultiplier ν) : b.toL2 =ᵐ[ν] b.value := MemLp.coeFn_toLp _

end BoundedMultiplier
variable {d : ℕ}

theorem cartesianSpacetimePotential_eq_projection (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))) :
    (cartesianSpacetimePotential o δ hδ N g b).toL2=
      cartesianSpacetimeCellIsometry o δ hδ N g
        ((cartesianSpacetimeCellIsometry o δ hδ N g).toContinuousLinearMap.adjoint b.toL2) := by
  let E := cartesianSpacetimeCellIsometry o δ hδ N g
  have hcoeff a : (E.toContinuousLinearMap.adjoint b.toL2) a=cartesianAveragedPotential o δ N g b a.1 a.2 := by
    rw [cartesianSpacetimeCellIsometry_adjoint_average,cartesianAveragedPotential_product_formula o δ hδ N g b a]
    apply congrArg ((g.dt*(∏ j, δ j))⁻¹ * ·)
    exact integral_congr_ae (ae_restrict_of_ae b.toL2_ae)
  apply Lp.ext
  filter_upwards [(cartesianSpacetimePotential o δ hδ N g b).toL2_ae,
    finiteCellLinear_ae (cartesianSpacetimeCell o δ N g) (cartesianSpacetimeCell_measurable o δ N g)
      (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j))) (E.toContinuousLinearMap.adjoint b.toL2)] with x hb hE
  rw [hb]
  change finiteCellFunction (cartesianSpacetimeCell o δ N g)
    (fun a => cartesianAveragedPotential o δ N g b a.1 a.2) x=
      (finiteCellLinear (cartesianSpacetimeCell o δ N g) (cartesianSpacetimeCell_measurable o δ N g)
        (mul_pos g.dt_pos (Finset.prod_pos (fun j _ => hδ j)))
        (E.toContinuousLinearMap.adjoint b.toL2)) x
  rw [hE]
  simp only [finiteCellFunction,hcoeff]

def fixedSpacetimePotential (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesianSpacetimePotential lo δ hδ N g b

theorem fixedSpacetimePotential_bound (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    (fixedSpacetimePotential T lo hi δ hδ N hbox g hT b).bound=b.bound := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesianSpacetimePotential_bound lo δ hδ N g b

theorem fixedSpacetimePotential_eq_projection (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    (fixedSpacetimePotential T lo hi δ hδ N hbox g hT b).toL2=
      fixedSpacetimeCellIsometry T lo hi δ hδ N hbox g hT
        ((fixedSpacetimeCellIsometry T lo hi δ hδ N hbox g hT).toContinuousLinearMap.adjoint b.toL2) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesianSpacetimePotential_eq_projection lo δ hδ N g b

theorem cartesianAveragedPotential_strong_convergence (T : ℝ) (hTpos : 0 ≤ T) (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi)))) :
    Tendsto (fun n => (fixedSpacetimePotential T lo hi (δ n) (hδ n) (N n) (hbox n) (g n) (hT n) b).toL2)
      atTop (𝓝 b.toL2) := by
  simp_rw [fixedSpacetimePotential_eq_projection]
  exact fixedSpacetimeCell_average_strong_convergence T hTpos lo hi δ hδ N hN hbox g hT h hh hstep hlim htlim b.toL2

end Carleman
