module
public import Carleman.Spatial.ExhaustionPeriodicDensity
public import Carleman.Spatial.HeatFieldEnergies
/-! A common inner-domain estimate passes to every original weak periodic state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem dirichletHeat_le_of_exhaustion (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n,T n⊆S)
    (hm : Monotone T) (hcover : S⊆⋃ n,T n)
    (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S))
    (ρn : ∀ n, SpatialProfile (volume.restrict (T n)))
    (hρ : ∀ n, ρ.value=ᵐ[volume.restrict (T n)] (ρn n).value)
    (w : TimeWeight) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (ε C : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (hCE : ∀ n (p : (boundedDirichletOriginalForm (hT n) hd (hb.subset (hTS n))).model.PeriodicGraph g),
      dirichletHeatLeft (hT n) hd (hb.subset (hTS n)) g (ρn n) w p ≤
      C*dirichletHeatRight (hT n) hd (hb.subset (hTS n)) g (ρn n) w ε W hW p) :
    ∀ p, dirichletHeatLeft hS hd hb g ρ w p ≤ C*dirichletHeatRight hS hd hb g ρ w ε W hW p := by
  have hc := isClosed_le (continuous_dirichletHeatLeft hS hd hb g ρ w hq)
    ((continuous_dirichletHeatRight hS hd hb g ρ w hq ε W hW).const_mul C)
  have hdense := dirichletExhaustionApproximable_dense hS hd hb T hT hTS g hm hcover
  have hall : ∀ p ∈ dirichletExhaustionApproximable hS hd hb T hT hTS g,
      dirichletHeatLeft hS hd hb g ρ w p ≤ C*dirichletHeatRight hS hd hb g ρ w ε W hW p := by
    intro p hp
    obtain ⟨P,hP⟩ := hp
    have hL := (continuous_heatFieldsLeft g ρ w hq).continuousAt.tendsto.comp hP
    have hR := ((continuous_heatFieldsRight g ρ w hq ε W hW).const_mul C).continuousAt.tendsto.comp hP
    have hn (n : ℕ) :
        heatFieldsLeft g ρ w (subdomainHeatFields S (T n) g
          (dirichletHeatFields (hT n) hd (hb.subset (hTS n)) g (P n))) ≤
        C*heatFieldsRight g ρ w ε W hW (subdomainHeatFields S (T n) g
          (dirichletHeatFields (hT n) hd (hb.subset (hTS n)) g (P n))) := by
      let F := dirichletHeatFields (hT n) hd (hb.subset (hTS n)) g (P n)
      calc
        heatFieldsLeft g ρ w (subdomainHeatFields S (T n) g F)=heatFieldsLeft g (ρn n) w F :=
          heatFieldsLeft_subdomain (hT n).measurableSet (hTS n) g ρ (ρn n) (hρ n) w F
        _ ≤ C*heatFieldsRight g (ρn n) w ε W hW F := hCE n (P n)
        _ = C*heatFieldsRight g ρ w ε W hW (subdomainHeatFields S (T n) g F) :=
          congrArg (C*·) (heatFieldsRight_subdomain (hT n).measurableSet (hTS n) g ρ (ρn n) (hρ n) w ε W hW F).symm
    exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hn)
  intro p
  exact (closure_minimal hall hc) (hdense p)

end Carleman
