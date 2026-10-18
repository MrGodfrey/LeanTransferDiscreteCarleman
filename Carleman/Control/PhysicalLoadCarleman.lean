module

public import Carleman.Control.PhysicalPotentialLoad
public import Carleman.Control.PhysicalPotentialAbsorption

/-! The actual periodic load estimate needed by physical observability.
Its supply from a numerical realization remains explicit. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.Physical
variable {Ω E X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] {ν : Measure Ω}

def physicalWeightedSq (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (v : Fin g.steps → Lp E 2 ν) : ℝ :=
  g.dt*∑ i, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (v i))^2

def physicalWeightedCubeSq (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (v : Fin g.steps → Lp E 2 ν) : ℝ :=
  g.dt*∑ i, w.q (g.nodeTime i)^3*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (v i))^2

def PhysicalLoadCarleman (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (A : X →L[ℝ] X) (R Bstar : X →ₗ[ℝ] Lp E 2 ν) (Γ : Lp E 2 ν →ₗ[ℝ] X) (CCE : ℝ) : Prop :=
  ∀ (z : Fin g.steps → X) (f : Fin g.steps → Lp E 2 ν),
    (∀ i, g.dMinus z i+A (z i) = Γ (f i)) →
    physicalWeightedCubeSq ρ w g (fun i => R (z i)) ≤
      CCE*(physicalWeightedSq ρ w g f+physicalWeightedCubeSq ρ w g (fun i => Bstar (z i)))

theorem cutoff_observation_budget (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (a rstar : ℝ) (hrstar : 0 < rstar) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar)
    (Bstar : X →ₗ[ℝ] Lp E 2 ν) (p : Fin (g.steps+1) → X) :
    physicalWeightedCubeSq ρ w g (fun i => Bstar (cutoffState g (cutoffNodes g a) p i)) ≤
      (6/rstar^3)*(g.dt*∑ i : Fin g.steps, ‖Bstar (p i.castSucc)‖^2) := by
  have hi (i : Fin g.steps) :
      w.q (g.nodeTime i)^3*((ρ.multiplier w 0 (g.nodeTime i)).seminorm
        (Bstar (cutoffState g (cutoffNodes g a) p i)))^2 ≤
      (6/rstar^3)*‖Bstar (p i.castSucc)‖^2 := by
    have hh := spatial_observation_weight_bound ρ w rstar (g.nodeTime i) hrstar hneg
      (Bstar (cutoffState g (cutoffNodes g a) p i))
    have hc := physicalCutoff_bounds g.period a ((i.val:ℝ)*g.dt)
    have hn : ‖Bstar (cutoffState g (cutoffNodes g a) p i)‖ ≤ ‖Bstar (p i.castSucc)‖ := by
      rw [cutoffState,map_smul,norm_smul,Real.norm_eq_abs]
      change |physicalCutoff g.period a ((i.val:ℝ)*g.dt)| * ‖Bstar (p i.castSucc)‖ ≤ _
      rw [abs_of_nonneg hc.1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc.2 (norm_nonneg (Bstar (p i.castSucc)))
    exact hh.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)
      (div_nonneg (by norm_num) (pow_pos hrstar 3).le))
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)) g.dt_pos.le
  simpa only [physicalWeightedCubeSq,← Finset.mul_sum,mul_left_comm] using hs

theorem cutoff_carleman_absorb [CompleteSpace X] (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (a M CI CCE : ℝ) (ha : 0 < a) (hM : 0 ≤ M) (hCI : 0 ≤ CI) (hCCE : 0 ≤ CCE)
    (hsmall : ∀ i : Fin g.steps, 2*CCE*M^2 ≤ w.q (g.nodeTime i)^3/2)
    (A : X →L[ℝ] X) (V : Fin g.steps → X →L[ℝ] X) (hSym : ∀ i, (A+V i).IsSymmetric)
    (R I Bstar : X →ₗ[ℝ] Lp E 2 ν) (Γ : Lp E 2 ν →ₗ[ℝ] X)
    (b : Fin g.steps → BoundedMultiplier ν) (hb : ∀ i, (b i).bound ≤ M)
    (hpot : ∀ i x, Γ ((b i).map (R x)) = V i x) (hI : ∀ x, Γ (I x) = x)
    (hIw : ∀ i x, (ρ.multiplier w 0 (g.nodeTime i)).seminorm (I x) ≤
      CI*(ρ.multiplier w 0 (g.nodeTime i)).seminorm (R x))
    (hce : PhysicalLoadCarleman ρ w g A R Bstar Γ CCE)
    (p : Fin (g.steps+1) → X) (hp : AdjointEquation g.dt (fun i => A+V i) p) :
    physicalWeightedCubeSq ρ w g (fun i => R (cutoffState g (cutoffNodes g a) p i)) ≤
      4*CCE*CI^2*physicalWeightedSq ρ w g (fun i => R (cutoffRemainder g (cutoffNodes g a) p i))+
      2*CCE*physicalWeightedCubeSq ρ w g (fun i => Bstar (cutoffState g (cutoffNodes g a) p i)) := by
  let z := cutoffState g (cutoffNodes g a) p
  let r := cutoffRemainder g (cutoffNodes g a) p
  let f := physicalCutoffLoad g a R I b p
  have he := hce z f (physical_cutoff_load_equation g a ha A V hSym R I Γ b hpot hI p hp)
  have hf := Finset.sum_le_sum (s := Finset.univ) (fun i _ => physical_cutoff_load_bound
    g a M CI hM hCI R I b hb (fun i => ρ.multiplier w 0 (g.nodeTime i)) hIw p i)
  have hload : physicalWeightedSq ρ w g f ≤
      2*M^2*physicalWeightedSq ρ w g (fun i => R (z i))+
      2*CI^2*physicalWeightedSq ρ w g (fun i => R (r i)) := by
    have hh := mul_le_mul_of_nonneg_left hf g.dt_pos.le
    simpa only [physicalWeightedSq,Finset.sum_add_distrib,← Finset.mul_sum,mul_add,mul_left_comm] using hh
  have habs : 2*CCE*M^2*physicalWeightedSq ρ w g (fun i => R (z i)) ≤
      physicalWeightedCubeSq ρ w g (fun i => R (z i))/2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hsmall i) (sq_nonneg
        ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (R (z i)))))
    have ht := mul_le_mul_of_nonneg_left hh g.dt_pos.le
    simpa only [physicalWeightedSq,physicalWeightedCubeSq,div_mul_eq_mul_div,Finset.sum_div,
      ← Finset.mul_sum,mul_div_assoc,mul_left_comm] using ht
  have hh := mul_le_mul_of_nonneg_left hload hCCE
  nlinarith only [he,hh,habs]

end Carleman.Physical
