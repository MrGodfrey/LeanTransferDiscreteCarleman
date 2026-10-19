module

public import Carleman.Spatial.BoxSmoothHeatEstimate
public import Carleman.Spatial.HeatTimeReflection

/-! The two original time signs on the same smooth box class, with one set of constants. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

def spaceTimeOrientedHeat (ε : ℝ) (u : (ℝ × SpatialCoordinates d) → ℝ)
    (tx : ℝ × SpatialCoordinates d) : ℝ :=
  ε*deriv (fun s => u (s,tx.2)) tx.1-spatialLaplacian (fun y => u (tx.1,y)) tx.2

theorem spaceTimeHeat_time_reflection_eq {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (T : ℝ) :
    spaceTimeHeat (fun tx => u (heatTimeReflection T tx))=
      (fun tx => spaceTimeOrientedHeat (-1) u (heatTimeReflection T tx)) := by
  funext tx
  rw [spaceTimeHeat_time_reflection hu]
  simp only [spaceTimeOrientedHeat,heatTimeReflection,neg_one_mul]

theorem box_smooth_gaussian_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ q : ℝ → ℝ, ContDiff ℝ ∞ q → Function.Periodic q T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |deriv q t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |deriv (deriv q) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      ∀ u : (ℝ × SpatialCoordinates (d+1)) → ℝ, ContDiff ℝ ∞ u → Function.Periodic u (T,0) →
      (∀ t : ℝ, ∀ x ∈ frontier (openCoordinateBox a b), u (t,x)=0) →
      let L := interiorGaussianHeatPhase c l q
      boxTimeIntegral a b T (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2)+
      boxTimeIntegral a b T (fun tx =>
        q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2) ≤
      C*(boxTimeIntegral a b T (fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat ε u tx)^2)+
        boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator
          (fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hforward⟩ :=
    box_smooth_gaussian_heat_estimate a b hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro T hT q hq hqp hqmin hq' hq'' ε hε u hu hup hub
  rcases hε with rfl | rfl
  · simpa only [spaceTimeOrientedHeat,one_mul,spaceTimeHeat] using
      hforward T hT q hq hqp hqmin hq' hq'' u hu hup hub
  · have hqr : ContDiff ℝ ∞ (fun t => q (T-t)) := hq.comp (contDiff_const.sub contDiff_id)
    have hur : ContDiff ℝ ∞ (fun tx => u (heatTimeReflection T tx)) :=
      hu.comp (heatTimeReflection_contDiff T)
    have hminr : ∀ t ∈ Icc 0 T, qc ≤ q (T-t) := fun t ht => hqmin (T-t) (time_reflection_mem_interval ht)
    have hq1r : ∀ t ∈ Icc 0 T, |deriv (fun s => q (T-s)) t| ≤ β*(q (T-t))^2 := by
      intro t ht
      rw [deriv_time_reflection hq,abs_neg]
      exact hq' (T-t) (time_reflection_mem_interval ht)
    have hq2r : ∀ t ∈ Icc 0 T, |deriv (deriv (fun s => q (T-s))) t| ≤ β^2*(q (T-t))^3 := by
      intro t ht
      rw [deriv_deriv_time_reflection hq]
      exact hq'' (T-t) (time_reflection_mem_interval ht)
    have hback := hforward T hT (fun t => q (T-t)) hqr (hqp.const_sub T) hminr hq1r hq2r
      (fun tx => u (heatTimeReflection T tx)) hur (heatTimeReflection_periodic hup)
      (fun t x hx => hub (T-t) x hx)
    dsimp only at hback ⊢
    rw [spaceTimeHeat_time_reflection_eq hu T] at hback
    let L := interiorGaussianHeatPhase c l q
    let F₀ := fun tx => (q tx.1)^3*(Real.exp (L tx))^2*(u tx)^2
    let F₁ := fun tx => q tx.1*(Real.exp (L tx))^2*‖gradient (fun y => u (tx.1,y)) tx.2‖^2
    let R := fun tx => (Real.exp (L tx)*spaceTimeOrientedHeat (-1) u tx)^2
    let O := (Prod.snd ⁻¹' W).indicator F₀
    change boxTimeIntegral a b T (fun tx => F₀ (heatTimeReflection T tx))+
      boxTimeIntegral a b T (fun tx => F₁ (heatTimeReflection T tx)) ≤
      C*(boxTimeIntegral a b T (fun tx => R (heatTimeReflection T tx))+
        boxTimeIntegral a b T (fun tx => O (heatTimeReflection T tx))) at hback
    simp only [boxTimeIntegral_reflection] at hback
    exact hback

end Carleman
