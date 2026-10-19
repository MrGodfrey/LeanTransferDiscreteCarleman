module

public import Carleman.Spatial.BoxC2HeatEstimate
public import Carleman.Weights.PeriodicC2Extension

/-! The original closed-interval C² time-weight class in the smooth box estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

theorem boxTimeIntegral_congr_on (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (he : ∀ t ∈ Icc 0 T, ∀ x ∈ openCoordinateBox a b, f (t,x)=g (t,x)) :
    boxTimeIntegral a b T f=boxTimeIntegral a b T g := by
  unfold boxTimeIntegral
  rw [Measure.prod_restrict]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)] with tx htx
  exact he tx.1 htx.1 tx.2 htx.2

theorem box_interval_C2_gaussian_heat_both_signs (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i)
    {W : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox a b) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc C : ℝ), c ∈ W ∧ 1 ≤ l ∧
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ T : ℝ, 0 < T → ∀ q : ℝ → ℝ, ContDiffOn ℝ 2 q (Icc 0 T) →
      q 0=q T → derivWithin q (Icc 0 T) 0=derivWithin q (Icc 0 T) T →
      derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) 0=
        derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) T →
      (∀ t ∈ Icc 0 T, qc ≤ q t) →
      (∀ t ∈ Icc 0 T, |derivWithin q (Icc 0 T) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 T, |derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) t| ≤ β^2*(q t)^3) →
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
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hglobal⟩ :=
    box_C2_gaussian_heat_both_signs a b hpos hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro T hT q hq he0 he1 he2 hqmin hq' hq'' ε hε u hu hup hub
  obtain ⟨Q,hQ,hQp,hQe⟩ := exists_periodic_C2_extension hT hq he0 he1 he2
  have hfinal := hglobal T hT Q hQ hQp
    (fun t ht => by rw [(hQe t ht).1]; exact hqmin t ht)
    (fun t ht => by rw [(hQe t ht).2.1,(hQe t ht).1]; exact hq' t ht)
    (fun t ht => by rw [(hQe t ht).2.2,(hQe t ht).1]; exact hq'' t ht) ε hε u hu hup hub
  have hI (F : ℝ × (ℝ × SpatialCoordinates (d+1)) → ℝ) :
      boxTimeIntegral a b T (fun tx => F (Q tx.1,tx))=
        boxTimeIntegral a b T (fun tx => F (q tx.1,tx)) := by
    apply boxTimeIntegral_congr_on
    intro t ht x _
    rw [(hQe t ht).1]
  have hO (F : ℝ × (ℝ × SpatialCoordinates (d+1)) → ℝ) :
      boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => F (Q tx.1,tx)))=
        boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => F (q tx.1,tx))) := by
    apply boxTimeIntegral_congr_on
    intro t ht x _
    by_cases hx : (t,x) ∈ Prod.snd ⁻¹' W
    · simp only [indicator_of_mem hx,(hQe t ht).1]
    · simp only [indicator_of_notMem hx]
  let F₀ := fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
    p.1^3*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*(u p.2)^2
  let F₁ := fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
    p.1*(Real.exp (p.1*interiorCarlemanProfile c l p.2.2))^2*‖gradient (fun y => u (p.2.1,y)) p.2.2‖^2
  let R := fun p : ℝ × (ℝ × SpatialCoordinates (d+1)) =>
    (Real.exp (p.1*interiorCarlemanProfile c l p.2.2)*spaceTimeOrientedHeat ε u p.2)^2
  change boxTimeIntegral a b T (fun tx => F₀ (Q tx.1,tx))+
    boxTimeIntegral a b T (fun tx => F₁ (Q tx.1,tx)) ≤
    C*(boxTimeIntegral a b T (fun tx => R (Q tx.1,tx))+
      boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => F₀ (Q tx.1,tx)))) at hfinal
  rw [hI F₀,hI F₁,hI R,hO F₀] at hfinal
  exact hfinal

end Carleman
