module

public import Carleman.Section4.ApproximationData

/-! Compose the proved Cea inequality with the original N3 bounds. The
actual reconstructed error has rate aE+ηA, and the reconstructed state is
stable, in the genuine nodal Sobolev energy norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d (2*m) ν S) (hDV : D ≤ V)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction V X) (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

theorem regularityNorm_nonneg (u : g.Sequence D) :
    0 ≤ regularityNorm hS hν hD g ρ w τ u :=
  Finset.sum_nonneg fun _ _ => g.l2Norm_nonneg _

/-- Both conclusions concern the actual solutions/reconstruction and actual
N3 approximation; only the already proved Cea conclusion is composed here. -/
theorem energy_rates_of_cea {aE a0 ηA Kc Cf : ℝ}
    (haE : 0 ≤ aE) (haE1 : aE ≤ 1) (hη : 0 ≤ ηA) (hη1 : ηA ≤ 1)
    (hKc : 0 ≤ Kc) (hCf : 0 ≤ Cf)
    (ha : WeightedApproximation hS hν hV hD hDV r g ρ w τ aE a0)
    (u : g.Sequence D) (z : g.Sequence X)
    (hcea : energyNorm hS hν hV g ρ w τ (fun i => r.R (z i-r.J (u i : Lp ℝ 2 ν))) ≤
      Kc*(Cf*energyNorm hS hν hV g ρ w τ
        (fun i => Submodule.inclusion hDV (u i)-r.Q (u i : Lp ℝ 2 ν))+
        ηA*energyNorm hS hν hV g ρ w τ (fun i => r.Q (u i : Lp ℝ 2 ν)))) :
    energyNorm hS hν hV g ρ w τ (fun i => Submodule.inclusion hDV (u i)-r.R (z i)) ≤
      (1+Kc*(Cf+(m+2)))*(aE+ηA)*regularityNorm hS hν hD g ρ w τ u ∧
    energyNorm hS hν hV g ρ w τ (fun i => r.R (z i)) ≤
      ((m+2)+Kc*(Cf+(m+2)))*regularityNorm hS hν hD g ρ w τ u := by
  let p := energySeminorm hS hν hV g ρ w τ
  let eta : g.Sequence V := fun i => Submodule.inclusion hDV (u i)-r.Q (u i : Lp ℝ 2 ν)
  let re : g.Sequence V := fun i => r.R (z i-r.J (u i : Lp ℝ 2 ν))
  let qu : g.Sequence V := fun i => r.Q (u i : Lp ℝ 2 ν)
  let G := regularityNorm hS hν hD g ρ w τ u
  have hG : 0 ≤ G := regularityNorm_nonneg hS hν hD g ρ w τ u
  have hηe : g.weightedNorm p eta ≤ aE*G := ha.nodal_energy hS hν hV hD hDV r g ρ w τ haE u
  have hQ : g.weightedNorm p qu ≤ (m+2:ℝ)*G :=
    (ha.nodal_Q hS hν hV hD hDV r g ρ w τ haE u).trans
      (mul_le_mul_of_nonneg_right (by linarith : (m+1+aE:ℝ) ≤ m+2) hG)
  have hRe : g.weightedNorm p re ≤ Kc*(Cf*aE+ηA*(m+2))*G := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hηe hCf) (mul_le_mul_of_nonneg_left hQ hη)
    have hh' := mul_le_mul_of_nonneg_left hh hKc
    change g.weightedNorm p re ≤ Kc*(Cf*g.weightedNorm p eta+ηA*g.weightedNorm p qu) at hcea
    exact hcea.trans (hh'.trans_eq (by ring))
  have herr : (fun i => Submodule.inclusion hDV (u i)-r.R (z i)) = eta-re := by
    funext i
    simp only [Pi.sub_apply,eta,re,map_sub,Reconstruction.Q_apply]
    abel
  have hstate : (fun i => r.R (z i)) = qu+re := by
    funext i
    simp only [Pi.add_apply,qu,re,map_sub,Reconstruction.Q_apply]
    abel
  constructor
  · change g.weightedNorm p _ ≤ _
    rw [herr]
    have hh := add_le_add hηe hRe
    have hc : aE+Kc*(Cf*aE+ηA*(m+2)) ≤ (1+Kc*(Cf+(m+2)))*(aE+ηA) := by
      have hm : 0 ≤ (m+2:ℝ) := by positivity
      nlinarith only [hη,mul_nonneg hKc (add_nonneg (mul_nonneg hCf hη) (mul_nonneg hm haE))]
    calc
      _ ≤ g.weightedNorm p eta+g.weightedNorm p re := g.weightedNorm_sub_le p eta re
      _ ≤ aE*G+Kc*(Cf*aE+ηA*(m+2))*G := hh
      _ = (aE+Kc*(Cf*aE+ηA*(m+2)))*G := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hG
  · change g.weightedNorm p _ ≤ _
    rw [hstate]
    have hc : Kc*(Cf*aE+ηA*(m+2)) ≤ Kc*(Cf+(m+2)) := by
      apply mul_le_mul_of_nonneg_left _ hKc
      have h1 := mul_le_mul_of_nonneg_left haE1 hCf
      have h2 := mul_le_mul_of_nonneg_right hη1 (show 0 ≤ (m+2:ℝ) by positivity)
      nlinarith only [h1,h2]
    have hh := add_le_add hQ (hRe.trans (mul_le_mul_of_nonneg_right hc hG))
    exact (g.weightedNorm_add_le p qu re).trans (hh.trans_eq (by ring))

end Carleman.Section4
