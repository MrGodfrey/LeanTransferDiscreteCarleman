module

public import Carleman.Control.PhysicalWeightedEnergy

/-! Actual bounded potential loads and the exact cutoff load equation. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical
variable {Ω E X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] {ν : Measure Ω}

theorem weighted_potential_bound (σ b : BoundedMultiplier ν) (M : ℝ)
    (hb : b.bound ≤ M) (u : Lp E 2 ν) : σ.seminorm (b.map u) ≤ M*σ.seminorm u := by
  have hh := (σ.mul b).seminorm_le_of_weight_le σ M (by
    filter_upwards [b.bounded] with x hx
    change |σ.value x*b.value x| ≤ M*|σ.value x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hx.trans hb) (abs_nonneg _)).trans_eq (mul_comm _ _)) u
  simpa only [BoundedMultiplier.seminorm_apply,BoundedMultiplier.mul_map] using hh

def physicalCutoffLoad (g : TimeGrid) (a : ℝ) (R I : X →ₗ[ℝ] Lp E 2 ν)
    (b : Fin g.steps → BoundedMultiplier ν) (p : Fin (g.steps+1) → X) (i : Fin g.steps) : Lp E 2 ν :=
  -(b i).map (R (cutoffState g (cutoffNodes g a) p i))-
    I (cutoffRemainder g (cutoffNodes g a) p i)

theorem physical_cutoff_load_equation [CompleteSpace X] (g : TimeGrid) (a : ℝ) (ha : 0 < a)
    (A : X →L[ℝ] X) (V : Fin g.steps → X →L[ℝ] X) (hSym : ∀ i, (A+V i).IsSymmetric)
    (R I : X →ₗ[ℝ] Lp E 2 ν) (Γ : Lp E 2 ν →ₗ[ℝ] X)
    (b : Fin g.steps → BoundedMultiplier ν)
    (hpot : ∀ i x, Γ ((b i).map (R x)) = V i x) (hI : ∀ x, Γ (I x) = x)
    (p : Fin (g.steps+1) → X) (hp : AdjointEquation g.dt (fun i => A+V i) p) (i : Fin g.steps) :
    g.dMinus (cutoffState g (cutoffNodes g a) p) i+A (cutoffState g (cutoffNodes g a) p i) =
      Γ (physicalCutoffLoad g a R I b p i) := by
  rw [physicalCutoffLoad,map_sub,map_neg,hpot,hI]
  exact concrete_cutoff_residual g a ha A V hSym p hp i

theorem physical_cutoff_load_bound (g : TimeGrid) (a M CI : ℝ) (hM : 0 ≤ M) (hCI : 0 ≤ CI)
    (R I : X →ₗ[ℝ] Lp E 2 ν) (b : Fin g.steps → BoundedMultiplier ν)
    (hb : ∀ i, (b i).bound ≤ M) (σ : Fin g.steps → BoundedMultiplier ν)
    (hI : ∀ i x, (σ i).seminorm (I x) ≤ CI*(σ i).seminorm (R x))
    (p : Fin (g.steps+1) → X) (i : Fin g.steps) :
    ((σ i).seminorm (physicalCutoffLoad g a R I b p i))^2 ≤
      2*M^2*((σ i).seminorm (R (cutoffState g (cutoffNodes g a) p i)))^2+
      2*CI^2*((σ i).seminorm (R (cutoffRemainder g (cutoffNodes g a) p i)))^2 := by
  have hp := weighted_potential_bound (σ i) (b i) M (hb i) (R (cutoffState g (cutoffNodes g a) p i))
  have hi := hI i (cutoffRemainder g (cutoffNodes g a) p i)
  have hs := map_sub_le_add (σ i).seminorm
    (-(b i).map (R (cutoffState g (cutoffNodes g a) p i)))
    (I (cutoffRemainder g (cutoffNodes g a) p i))
  rw [map_neg_eq_map] at hs
  have hl : (σ i).seminorm (physicalCutoffLoad g a R I b p i) ≤
      M*(σ i).seminorm (R (cutoffState g (cutoffNodes g a) p i))+
      CI*(σ i).seminorm (R (cutoffRemainder g (cutoffNodes g a) p i)) := hs.trans (add_le_add hp hi)
  have hsq := (sq_le_sq₀ (apply_nonneg _ _) (add_nonneg
    (mul_nonneg hM (apply_nonneg _ _)) (mul_nonneg hCI (apply_nonneg _ _)))).mpr hl
  nlinarith only [hsq,sq_nonneg (M*(σ i).seminorm (R (cutoffState g (cutoffNodes g a) p i))-
    CI*(σ i).seminorm (R (cutoffRemainder g (cutoffNodes g a) p i)))]

end Carleman.Physical
