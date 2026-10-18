module

public import Carleman.Section3.SolvedProfiles

/-! One common threshold for the four genuine estimates. These are conclusions,
not hypotheses replacing the original analytic assumptions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section3
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)
  (a : V → V → ℝ) (ρ : SpatialProfile ν) (c C Ccomm β τStar : ℝ)

structure ProfileEstimates (L₀ δ K : ℝ) : Prop where
  shift : ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
    (L τ : ℝ) (hLpos : 0 < L), L₀ ≤ L → |τ| ≤ τStar →
    AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
    ContinuousEstimate hS hν b hD g s w ρ τ K h.aestronglyMeasurable (h.shiftMultiplier m L hLpos)
  euler : ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
    (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
    EulerEstimate hS hν b hD g s w ρ L τ K
  frozen : ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
    (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
    ContinuousEstimate hS hν b hD g s w ρ τ K h.aestronglyMeasurable
      (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m)))
  temporal : ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
    (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
    AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
    AllowedWeightData hS hν hV hD a b.operator ρ.neg w (-τ) c C Ccomm →
    TemporalEstimate hS hν b hV hDV g s w ρ L τ K

theorem ProfileEstimates.mono {L₀ δ K L₁ δ₁ K₁ : ℝ}
    (h : ProfileEstimates hS hν b hV hDV hD a ρ c C Ccomm β τStar L₀ δ K)
    (hL : L₀ ≤ L₁) (hδ : δ₁ ≤ δ) (hK : K ≤ K₁) :
    ProfileEstimates hS hν b hV hDV hD a ρ c C Ccomm β τStar L₁ δ₁ K₁ where
  shift g s w hw L τ hp hLL ht hd :=
    (h.shift g s w hw L τ hp (hL.trans hLL) ht hd).mono hS hν b hD hK
  euler g s w hw L τ hLL hm ht hd :=
    (h.euler g s w hw L τ (hL.trans hLL) (hm.trans hδ) ht hd).mono hS hν b hD hK
  frozen g s ex w hw L τ hLL hm ht hd :=
    (h.frozen g s ex w hw L τ (hL.trans hLL) (hm.trans hδ) ht hd).mono hS hν b hD hK
  temporal g s w hw L τ hLL hm ht hd hi :=
    (h.temporal g s w hw L τ (hL.trans hLL) (hm.trans hδ) ht hd hi).mono hS hν b hV hDV hK

end Carleman.Section3
namespace Carleman.Section3
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  {V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))}
  (hV : V ≤ sobolevSubspace d m (volume.restrict S) S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V, a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 (volume.restrict S)))
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)

include hρ htest in
set_option maxHeartbeats 1600000 in
theorem profile_uniform (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < K ∧
      ProfileEstimates hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hV hDV hD a ρ c C Ccomm β τStar L₀ δ K := by
  obtain ⟨Ls,Ks,hLs,hKs,hs⟩ := shift_solved_uniform hΩ b hV hD a ρ hρ hm Creg c C Ccomm β τStar hCcomm hβ hτStar hell
  obtain ⟨Le,de,Ke,hLe,hde,hKe,he⟩ := euler_solved_uniform hΩ b hV hD a ρ hρ hm Creg c C Ccomm β τStar hCcomm hβ hτStar hell
  obtain ⟨Lf,df,Kf,hLf,hdf,hKf,hf⟩ := frozen_solved_uniform hΩ b hV hD a ρ hρ hm Creg c C Ccomm β τStar hCcomm hβ hτStar hell
  obtain ⟨Lt,dt,hLt,hdt,ht⟩ := temporal_arbitrary_uniform hΩ b hV hDV hD a htest ρ hρ hm Creg c C Ccomm β τStar hc hCcomm hβ hτStar hell
  let L₀ := max (max Ls Le) (max Lf Lt)
  let δ := min 1 (min de (min df dt))
  let K := max (max Ks Ke) (max Kf (max 2160 (Real.sqrt (466560/c))))
  have hLs' : Ls ≤ L₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hLe' : Le ≤ L₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hLf' : Lf ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hLt' : Lt ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hde' : δ ≤ de := (min_le_right _ _).trans (min_le_left _ _)
  have hdf' : δ ≤ df := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdt' : δ ≤ dt := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKs' : Ks ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKe' : Ke ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKf' : Kf ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKt' : max 2160 (Real.sqrt (466560/c)) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L₀,δ,K,hLs.trans hLs',lt_min zero_lt_one (lt_min hde (lt_min hdf hdt)),min_le_left _ _,hKs.trans_le hKs',?_⟩
  constructor
  · intro g s w h L τ hp hL hτ hd
    exact (hs g s w h L τ hp (hLs'.trans hL) hτ hd).mono _ _ _ _ hKs'
  · intro g s w h L τ hL hm hτ hd
    exact (he g s w h L τ (hLe'.trans hL) (hm.trans hde') hτ hd).mono _ _ _ _ hKe'
  · intro g s ex w h L τ hL hm hτ hd
    exact (hf g s ex w h L τ (hLf'.trans hL) (hm.trans hdf') hτ hd).mono _ _ _ _ hKf'
  · intro g s w h L τ hL hm hτ hd hi
    exact (ht g s w h L τ (hLt'.trans hL) (hm.trans hdt') hτ hd hi).mono _ _ _ _ _ hKt'
end Carleman.Section3
