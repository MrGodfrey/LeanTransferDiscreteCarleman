module

public import Carleman.Spatial.HigherCoefficientForm
public import Carleman.Spatial.HigherDirichletProduct
public import Carleman.Spatial.CoefficientConjugationError
public import Carleman.Weights.IntrinsicConjugation
/-! Original coercivity implies the uniform lower bound for the actual
allowed exponential weights on the full H₀ᵐ space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}

theorem higherDirichlet_smoothProduct_exists (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : HigherDirichletEnergy S m) :
    ∃ z : HigherDirichletEnergy S m,
      WeakSobolevJet.value (higherDirichletToJet S m z)=w.map (WeakSobolevJet.value (higherDirichletToJet S m u)) := by
  have hm := boundedSmooth_map_mem_higherDirichlet hS w hw
    (WeakSobolevJet.value (higherDirichletToJet S m u)) u.property
  have he := (conformingEmbed_range (m := m) (S := S) (higherDirichletSubspace S m)
    (higherDirichletSubspace_sobolev S m)).ge hm
  exact he

variable {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem allowedWeight_inverse_relative_uniform (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    {ρ : SpatialCoordinates d → ℝ} (hρ : BoundedSmoothOn ρ S) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier ν, w.value=(fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      BoundedSmoothOn w.value S ∧ ∃ ξ : BoundedMultiplier ν, BoundedSmoothOn ξ.value S ∧
        (∀ᵐ x ∂ν, w.value x*ξ.value x=1) ∧
        (∀ l : List (Fin d), l.length ≤ m → ∀ᵐ x ∂ν,
          |ξ.value x*wordDerivative l w.value x| ≤ C*q^l.length) ∧
        (∀ l : List (Fin d), l.length ≤ m → ∀ᵐ x ∂ν,
          |w.value x*wordDerivative l ξ.value x| ≤ C*q^l.length) := by
  obtain ⟨C,hC,hbound⟩ := hρ.allowedWeight_word_uniform hS m
  refine ⟨C,hC,?_⟩
  intro q hq τ eta heta w hw
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hi := hρ.allowedWeight hS hq (-τ) (-eta) (by simpa using heta)
  let ξ := intrinsicWordMultiplier hS hν hi []
  have hξ : ξ.value=(fun x => q^(-τ)*Real.exp (q*((-eta)*ρ x))) := by
    exact wordDerivative_nil _
  have hinv (x : SpatialCoordinates d) : w.value x*ξ.value x=1 := by
    rw [hw,hξ,Real.rpow_neg hq0.le]
    dsimp only
    have he : q*(-eta*ρ x)=-(q*(eta*ρ x)) := by ring
    rw [he,Real.exp_neg]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hq0 τ)]
  have hwS : BoundedSmoothOn w.value S := by rw [hw]; exact hρ.allowedWeight hS hq τ eta heta
  have hξS : BoundedSmoothOn ξ.value S := by rw [hξ]; exact hi
  refine ⟨hwS,ξ,hξS,Filter.Eventually.of_forall hinv,?_,?_⟩
  · intro l hl
    filter_upwards [hν] with x hx
    have hb := hbound q hq τ eta heta l hl x hx
    have hpos : 0 < ξ.value x := by rw [hξ]; positivity
    rw [abs_mul,abs_of_pos hpos,hw]
    calc
      _ ≤ ξ.value x*(C*q^l.length*(q^τ*Real.exp (q*(eta*ρ x)))) := mul_le_mul_of_nonneg_left hb hpos.le
      _ = C*q^l.length := by
        rw [←congrFun hw x]
        calc
          _ = (C*q^l.length)*(w.value x*ξ.value x) := by ring
          _ = _ := by rw [hinv,mul_one]
  · intro l hl
    filter_upwards [hν] with x hx
    have hb := hbound q hq (-τ) (-eta) (by simpa using heta) l hl x hx
    have hpos : 0 < w.value x := by rw [hw]; positivity
    rw [abs_mul,abs_of_pos hpos,hξ]
    calc
      _ ≤ w.value x*(C*q^l.length*(q^(-τ)*Real.exp (q*((-eta)*ρ x)))) := mul_le_mul_of_nonneg_left hb hpos.le
      _ = C*q^l.length := by rw [←congrFun hξ x,mul_left_comm,hinv,mul_one]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 8000000 in
theorem higherCoefficientForm_allowedWeight_lower
    (hΩ : IsBoundedLipschitzDomain S F) {ρ : SpatialCoordinates d → ℝ}
    (hρ : BoundedSmoothOn ρ S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hcoer : ∃ c > (0 : ℝ), ∀ u : HigherDirichletEnergy S m, c*‖u‖*‖u‖ ≤ higherCoefficientForm S m a u u) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier (volume.restrict S),
        w.value=(fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      ∀ v z : HigherDirichletEnergy S m,
        WeakSobolevJet.value (higherDirichletToJet S m z)=
          w.map (w.map (WeakSobolevJet.value (higherDirichletToJet S m v))) →
        c*(WeakSobolevJet.weightedNorm q w (higherDirichletToJet S m v))^2-
          C*(q^m*w.seminorm (WeakSobolevJet.value (higherDirichletToJet S m v)))^2 ≤
          higherCoefficientForm S m a v z := by
  have hS := hΩ.isOpen
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  obtain ⟨c₀,hc₀,hcoer⟩ := hcoer
  obtain ⟨J,hJ,hweights⟩ := allowedWeight_inverse_relative_uniform hS hν hρ m
  obtain ⟨D,hD,hconjugate⟩ := intrinsic_allowedWeight_parameterNorm_uniform (n := m) hS hν hρ
  obtain ⟨I,hI,hinterpolate⟩ := WeakSobolevJet.boundedLipschitz_parameter_interpolation hΩ m
  let A := ∑ α, ∑ β, (a α β).bound
  have hA : 0 ≤ A := Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun β _ => (a α β).bound_nonneg
  let K := (2:ℝ)^m*J
  have hK : 0 ≤ K := mul_nonneg (by positivity) hJ.le
  let B := A*K*(K+2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let B₁ := 1+B
  have hB₁ : 0 < B₁ := by dsimp [B₁]; positivity
  let δ := c₀/(2*B₁)
  have hδ : 0 < δ := div_pos hc₀ (mul_pos (by norm_num) hB₁)
  have hδeq : B₁*δ=c₀/2 := by dsimp [δ]; field_simp
  obtain ⟨E,hE,hlower⟩ := WeakSobolevJet.boundedLipschitz_lowerParameter_product_small hΩ m hδ
  let G := 2*(D*I)^2
  have hG : 0 < G := by dsimp [G]; positivity
  have hcG : 0 < c₀/(2*G) := div_pos hc₀ (mul_pos (by norm_num) hG)
  have hGeq : (c₀/(2*G))*G=c₀/2 := by field_simp
  refine ⟨c₀/(2*G),hcG,B₁*E+c₀/2,by positivity,?_⟩
  intro q hq τ eta heta w hw v z hz
  obtain ⟨hwS,ξ,hξS,hinv,hbw,hbξ⟩ := hweights q hq τ eta heta w hw
  obtain ⟨u,hu⟩ := higherDirichlet_smoothProduct_exists hS w hwS v
  let ju := higherDirichletToJet S m u
  let jv := higherDirichletToJet S m v
  let jz := higherDirichletToJet S m z
  let L := WeakSobolevJet.lowerParameterNorm q ju
  let R := WeakSobolevJet.parameterNorm q BoundedMultiplier.one ju
  let H := ‖u‖
  let M := q^m*‖WeakSobolevJet.value ju‖
  let N := WeakSobolevJet.weightedNorm q w jv
  have hq0 := zero_le_one.trans hq
  have hL : 0 ≤ L := WeakSobolevJet.lowerParameterNorm_nonneg hq0 ju
  have hR : 0 ≤ R := WeakSobolevJet.parameterNorm_nonneg hq0 _ ju
  have hH : 0 ≤ H := norm_nonneg _
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg hq0 _) (norm_nonneg _)
  have hN : 0 ≤ N := WeakSobolevJet.weightedNorm_nonneg q w jv
  have hn : ‖ju‖ ≤ H := SobolevHilbert.toJet_norm_le u.val
  have hi : ∀ᵐ x ∂volume.restrict S, ξ.value x*w.value x=1 := hinv.mono fun x hx => by rw [mul_comm]; exact hx
  have hv : WeakSobolevJet.value jv=ξ.map (WeakSobolevJet.value ju) := by
    rw [hu]
    exact (ξ.map_inverse w hi _).symm
  have hz' : WeakSobolevJet.value jz=w.map (WeakSobolevJet.value ju) := by rw [hu]; exact hz
  have herr := coefficientJetForm_smooth_conjugation_error hS hν a w ξ hwS hξS hinv hq hJ.le hbw hbξ ju jv jz hv hz'
  have hprod : L*R ≤ δ*H^2+E*M^2 :=
    (hlower q hq ju).trans (add_le_add (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hH).mpr hn) hδ.le) le_rfl)
  have hsmall : B*L*R ≤ c₀/2*H^2+(B₁*E)*M^2 := by
    calc
      _ ≤ B₁*(L*R) := by
        have hh := mul_le_mul_of_nonneg_right (show B ≤ B₁ by dsimp [B₁]; linarith) (mul_nonneg hL hR)
        simpa only [mul_assoc] using hh
      _ ≤ B₁*(δ*H^2+E*M^2) := mul_le_mul_of_nonneg_left hprod hB₁.le
      _ = _ := by rw [mul_add,←mul_assoc,hδeq]; ring
  have he : |higherCoefficientForm S m a v z-higherCoefficientForm S m a u u| ≤
      c₀/2*H^2+(B₁*E)*M^2 := herr.trans hsmall
  have hcoercive : c₀*H^2 ≤ higherCoefficientForm S m a u u := by
    simpa only [H,pow_two,mul_assoc] using hcoer u
  have hform : c₀/2*H^2-(B₁*E)*M^2 ≤ higherCoefficientForm S m a v z := by
    have hh := (abs_le.mp he).1
    nlinarith only [hcoercive,hh]
  have hIP : R ≤ I*(H+M) := by
    have hh : R ≤ I*(‖ju‖+M) := by
      simpa only [R,M,WeakSobolevJet.parameterNorm,BoundedMultiplier.one_seminorm] using hinterpolate q hq ju
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hn le_rfl) (zero_le_one.trans hI))
  have hNP : N ≤ D*R :=
    (WeakSobolevJet.weightedNorm_le_parameterNorm hq0 w jv).trans
      (hconjugate q hq τ eta heta w hw jv ju hu).2
  have hNH : N ≤ (D*I)*(H+M) := hNP.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hIP hD.le)
  have hN2 : N^2 ≤ G*(H^2+M^2) := by
    have hh := (sq_le_sq₀ hN (mul_nonneg (mul_nonneg hD.le (zero_le_one.trans hI)) (add_nonneg hH hM))).mpr hNH
    rw [mul_pow] at hh
    have hs : (H+M)^2 ≤ 2*(H^2+M^2) := by nlinarith [sq_nonneg (H-M)]
    exact hh.trans (calc
      _ ≤ (D*I)^2*(2*(H^2+M^2)) := mul_le_mul_of_nonneg_left hs (sq_nonneg (D*I))
      _ = G*(H^2+M^2) := by dsimp [G]; ring)
  have hscaled : (c₀/(2*G))*N^2 ≤ c₀/2*(H^2+M^2) := by
    calc
      _ ≤ (c₀/(2*G))*(G*(H^2+M^2)) := mul_le_mul_of_nonneg_left hN2 hcG.le
      _ = ((c₀/(2*G))*G)*(H^2+M^2) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hGeq]
  have hm : q^m*w.seminorm (WeakSobolevJet.value jv)=M := by
    dsimp [M]
    rw [hu]
    rfl
  change (c₀/(2*G))*N^2-(B₁*E+c₀/2)*(q^m*w.seminorm (WeakSobolevJet.value jv))^2 ≤ _
  rw [hm]
  nlinarith only [hform,hscaled]


set_option maxHeartbeats 8000000 in
theorem higherCoefficientForm_closure_weighted_coercivity
    (hΩ : IsBoundedLipschitzDomain S F) {ρ : SpatialCoordinates d → ℝ}
    (hρ : SmoothOnClosure ρ S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hcoer : ∃ c > (0 : ℝ), ∀ u : HigherDirichletEnergy S m, c*‖u‖*‖u‖ ≤ higherCoefficientForm S m a u u) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier (volume.restrict S),
        w.value=(fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      ∀ v : HigherDirichletEnergy S m, ∃ z : HigherDirichletEnergy S m,
        WeakSobolevJet.value (higherDirichletToJet S m z)=
          w.map (w.map (WeakSobolevJet.value (higherDirichletToJet S m v))) ∧
        c*(WeakSobolevJet.weightedNorm q w (higherDirichletToJet S m v))^2-
          C*(q^m*w.seminorm (WeakSobolevJet.value (higherDirichletToJet S m v)))^2 ≤
          higherCoefficientForm S m a v z := by
  have hρb := hρ.boundedSmoothOn hΩ.isBounded
  obtain ⟨c,hc,C,hC,hbound⟩ := higherCoefficientForm_allowedWeight_lower hΩ hρb a hcoer
  refine ⟨c,hc,C,hC,?_⟩
  intro q hq τ eta heta w hw v
  have hwS : BoundedSmoothOn w.value S := by rw [hw]; exact hρb.allowedWeight hΩ.isOpen hq τ eta heta
  obtain ⟨u,hu⟩ := higherDirichlet_smoothProduct_exists hΩ.isOpen w hwS v
  obtain ⟨z,hz⟩ := higherDirichlet_smoothProduct_exists hΩ.isOpen w hwS u
  have hz' : WeakSobolevJet.value (higherDirichletToJet S m z)=
      w.map (w.map (WeakSobolevJet.value (higherDirichletToJet S m v))) := by rw [hz,hu]
  exact ⟨z,hz',hbound q hq τ eta heta w hw v z hz'⟩

end Carleman
