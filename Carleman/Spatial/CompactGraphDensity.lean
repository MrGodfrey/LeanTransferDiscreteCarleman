module
public import Carleman.Spatial.CompactHalfspaceDensity
/-! Actual inverse graph transport and strong zero-boundary H² approximation
for compactly supported original states on both global graph sides. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
namespace WeakSobolevJet
variable {d : ℕ} {T : Set (SpatialCoordinates d)}
variable (hT : IsOpen T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
  {C : NNReal} (hC : LipschitzWith C ψ)
  (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
  {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)

include hT hC hB in
theorem graphShearInverseH2_value_exists
    (V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    ∃ U : WeakSobolevJet d 2 (volume.restrict T) T,
      value U=homeomorphPullbackLp F.symm
        ((spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T).symm F.toMeasurableEquiv) (value V) ∧
      (truncate (by decide : 1≤2) V∈dirichletJetSpace (F ⁻¹' T) →
        truncate (by decide : 1≤2) U∈dirichletJetSpace T) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let S := F ⁻¹' T
  have hS : IsOpen S := hT.preimage F.continuous
  have hntrans (x : SpatialCoordinates d) (t : ℝ) : -(ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r))= -ψ x :=
    congrArg Neg.neg (htrans x t)
  have hBn (i : Fin d) : LipschitzWith (B i) (graphSlopeMultiplier (fun x => -ψ x) hψ.neg hC.neg i).value := by
    rw [graphSlopeMultiplier_neg]
    exact (hB i).neg
  let G := spatialGraphShear r (fun x => -ψ x) hψ.neg.continuous hntrans
  have hh : ∃ U : WeakSobolevJet d 2 (volume.restrict (G ⁻¹' S)) (G ⁻¹' S),
      value U =ᵐ[volume.restrict (G ⁻¹' S)] value V ∘ G ∧
      (truncate (by decide : 1≤2) V∈dirichletJetSpace S →
        truncate (by decide : 1≤2) U∈dirichletJetSpace (G ⁻¹' S)) := by
    obtain ⟨U,hU,_⟩ := exists_graphShearPullback_H2 hS r (fun x => -ψ x) hψ.neg hC.neg hntrans hBn V
    refine ⟨U,?_,?_⟩
    · have hv := congrArg value hU
      rw [truncate_value,graphShearPullback_value,truncate_value] at hv
      rw [hv]
      exact homeomorphPullbackLp_ae _ _ _
    · intro hv
      rw [hU]
      exact graphShearPullback_dirichlet hS r (fun x => -ψ x) hψ.neg hC.neg hntrans _ hv
  have hG : G=F.symm := spatialGraphShear_neg_eq_symm r ψ hψ.continuous htrans
  have hdom : F.symm ⁻¹' S=T := by
    ext x
    change F (F.symm x)∈T ↔ x∈T
    rw [F.apply_symm_apply]
  rw [hG,hdom] at hh
  obtain ⟨U,hU,hD⟩ := hh
  refine ⟨U,?_,hD⟩
  apply Lp.ext
  exact hU.trans (homeomorphPullbackLp_ae _ _ _).symm

def graphShearInverseH2 :
    WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) →L[ℝ] WeakSobolevJet d 2 (volume.restrict T) T :=
  valueLiftCLM hT
    (homeomorphPullbackLp (spatialGraphShear r ψ hψ.continuous htrans).symm
      ((spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T).symm
        (spatialGraphShear r ψ hψ.continuous htrans).toMeasurableEquiv)).toContinuousLinearMap
    (fun V => (graphShearInverseH2_value_exists hT r ψ hψ hC htrans hB V).imp (fun _ h => h.1))

theorem graphShearInverseH2_value
    (V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)) :
    value (graphShearInverseH2 hT r ψ hψ hC htrans hB V)=
      homeomorphPullbackLp (spatialGraphShear r ψ hψ.continuous htrans).symm
        ((spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T).symm
          (spatialGraphShear r ψ hψ.continuous htrans).toMeasurableEquiv) (value V) :=
  valueLiftCLM_value _ _ _ V

theorem graphShearInverseH2_dirichlet
    (V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
    (hV : truncate (by decide : 1≤2) V∈dirichletJetSpace (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)) :
    truncate (by decide : 1≤2) (graphShearInverseH2 hT r ψ hψ hC htrans hB V)∈dirichletJetSpace T := by
  obtain ⟨U,hU,hD⟩ := graphShearInverseH2_value_exists hT r ψ hψ hC htrans hB V
  have he : graphShearInverseH2 hT r ψ hψ hC htrans hB V=U := by
    apply value_injective hT (ae_restrict_mem hT.measurableSet)
    exact (graphShearInverseH2_value hT r ψ hψ hC htrans hB V).trans hU.symm
  rw [he]
  exact hD hV

theorem graphShearInverseH2_left_inverse (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    graphShearInverseH2 hT r ψ hψ hC htrans hB (graphShearH2Pullback hT r ψ hψ hC htrans hB U)=U := by
  apply value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [graphShearInverseH2_value,graphShearH2Pullback_value,homeomorphPullbackLp_inverse]

theorem graphShearInverseH2_right_inverse
    (V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)) :
    graphShearH2Pullback hT r ψ hψ hC htrans hB (graphShearInverseH2 hT r ψ hψ hC htrans hB V)=V := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  have hS := hT.preimage F.continuous
  apply value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [graphShearH2Pullback_value]
  apply (homeomorphPullbackLp F.symm
    ((spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T).symm F.toMeasurableEquiv)).injective
  rw [homeomorphPullbackLp_inverse,graphShearInverseH2_value]

theorem graphShearInverseH2_tendsto
    {V : ℕ → WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)}
    {v : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)} (ht : Tendsto V atTop (𝓝 v)) :
    Tendsto (fun n => graphShearInverseH2 hT r ψ hψ hC htrans hB (V n)) atTop
      (𝓝 (graphShearInverseH2 hT r ψ hψ hC htrans hB v)) :=
  ((graphShearInverseH2 hT r ψ hψ hC htrans hB).continuous.tendsto v).comp ht

theorem graphShearH2Pullback_globalTest (φ : SpatialTest (univ : Set (SpatialCoordinates d))) :
    graphShearH2Pullback hT r ψ hψ hC htrans hB (φ.allOrderJetOn T 2)=
      (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans)
        (spatialGraphShear_contDiff r ψ hψ htrans) (subset_univ _)).allOrderJetOn
          (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) 2 := by
  have hS := hT.preimage (spatialGraphShear r ψ hψ.continuous htrans).continuous
  apply value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [graphShearH2Pullback_value,SpatialTest.allOrderJetOn_value,SpatialTest.allOrderJetOn_value,
    SpatialTest.pullbackSmoothHomeomorph_toLp _ _ _ _ (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)]

theorem graphShearInverseH2_globalTest (φ : SpatialTest (univ : Set (SpatialCoordinates d))) :
    graphShearInverseH2 hT r ψ hψ hC htrans hB
      (φ.allOrderJetOn (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) 2)=
      (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans).symm
        (spatialGraphShear_symm_contDiff r ψ hψ htrans) (subset_univ _)).allOrderJetOn T 2 := by
  apply value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [graphShearInverseH2_value,SpatialTest.allOrderJetOn_value,SpatialTest.allOrderJetOn_value,
    SpatialTest.pullbackSmoothHomeomorph_toLp _ _ _ _
      ((spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T).symm
        (spatialGraphShear r ψ hψ.continuous htrans).toMeasurableEquiv)]
end WeakSobolevJet
variable {d : ℕ} {T K : Set (SpatialCoordinates d)}

theorem exists_compact_graphShear_strong_h2_approximation
    (hT : IsOpen T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (upper : Bool) (hhalf : spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T=signedCoordinateHalfspace r upper)
    (hK : IsCompact K) (u : dirichletH2JetSpace T)
    (hu : ∀ᵐ x ∂volume.restrict T, x∉K → WeakSobolevJet.value u.val x=0) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier T, (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2) ((U n).allOrderJetOn T 2)∈dirichletJetSpace T) ∧
      Tendsto (fun n => (U n).allOrderJetOn T 2) atTop (𝓝 u.val) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let S := F ⁻¹' T
  let V := WeakSobolevJet.graphShearH2Pullback hT r ψ hψ hC htrans hB u.val
  have hD : WeakSobolevJet.truncate (by decide : 1≤2) V∈dirichletJetSpace S :=
    WeakSobolevJet.graphShearH2Pullback_dirichlet hT r ψ hψ hC htrans hB u.val u.property
  have hk : IsCompact (F ⁻¹' K) := F.isCompact_preimage.mpr hK
  have hv : ∀ᵐ x ∂volume.restrict S, x∉F ⁻¹' K → WeakSobolevJet.value V x=0 := by
    have hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
    filter_upwards [WeakSobolevJet.graphShearH2Pullback_ae hT r ψ hψ hC htrans hB u.val,
      hm.quasiMeasurePreserving.ae hu] with x hx hux
    intro hxK
    exact hx.trans (hux hxK)
  have hex := exists_compact_halfspace_strong_h2_approximation r upper hk
  rw [← hhalf] at hex
  obtain ⟨A,hA,hAD,hlim⟩ := hex ⟨V,hD⟩ hv
  let U (n : ℕ) := (A n).pullbackSmoothHomeomorph F.symm
    (spatialGraphShear_symm_contDiff r ψ hψ htrans) (subset_univ _)
  have he (n : ℕ) : WeakSobolevJet.graphShearInverseH2 hT r ψ hψ hC htrans hB
      ((A n).allOrderJetOn S 2)=(U n).allOrderJetOn T 2 :=
    WeakSobolevJet.graphShearInverseH2_globalTest hT r ψ hψ hC htrans hB (A n)
  refine ⟨U,?_,?_,?_⟩
  · intro n x hx
    change (A n).value (F.symm x)=0
    apply hA n
    change F.symm x∈frontier (F ⁻¹' T)
    rw [← F.preimage_frontier]
    change F (F.symm x)∈frontier T
    simpa only [F.apply_symm_apply] using hx
  · intro n
    rw [← he]
    exact WeakSobolevJet.graphShearInverseH2_dirichlet hT r ψ hψ hC htrans hB _ (hAD n)
  · have hc := WeakSobolevJet.graphShearInverseH2_tendsto hT r ψ hψ hC htrans hB hlim
    change Tendsto (fun n => WeakSobolevJet.graphShearInverseH2 hT r ψ hψ hC htrans hB
      ((A n).allOrderJetOn S 2)) atTop (𝓝 (WeakSobolevJet.graphShearInverseH2 hT r ψ hψ hC htrans hB V)) at hc
    have hfun : (fun n => WeakSobolevJet.graphShearInverseH2 hT r ψ hψ hC htrans hB
      ((A n).allOrderJetOn S 2))=(fun n => (U n).allOrderJetOn T 2) := funext he
    rw [hfun] at hc
    simpa only [V,WeakSobolevJet.graphShearInverseH2_left_inverse] using hc

def graphCoordinateSide (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (upper : Bool) : Set (SpatialCoordinates d) :=
  if upper then {x | ψ x<x r} else {x | x r<ψ x}

theorem graphCoordinateSide_isOpen (r : Fin d) {ψ : SpatialCoordinates d → ℝ}
    (hψ : Continuous ψ) (upper : Bool) : IsOpen (graphCoordinateSide r ψ upper) := by
  cases upper
  · exact isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r) hψ
  · exact isOpen_lt hψ (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)

theorem graphCoordinateSide_preimage (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (upper : Bool) :
    spatialGraphShear r ψ hψ htrans ⁻¹' graphCoordinateSide r ψ upper=signedCoordinateHalfspace r upper := by
  cases upper
  · exact spatialGraphShear_hypograph r ψ hψ htrans
  · exact spatialGraphShear_halfspace r ψ hψ htrans

theorem exists_compact_graphSide_strong_h2_approximation
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (upper : Bool) (hK : IsCompact K) (u : dirichletH2JetSpace (graphCoordinateSide r ψ upper))
    (hu : ∀ᵐ x ∂volume.restrict (graphCoordinateSide r ψ upper), x∉K → WeakSobolevJet.value u.val x=0) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier (graphCoordinateSide r ψ upper), (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2)
        ((U n).allOrderJetOn (graphCoordinateSide r ψ upper) 2)∈dirichletJetSpace (graphCoordinateSide r ψ upper)) ∧
      Tendsto (fun n => (U n).allOrderJetOn (graphCoordinateSide r ψ upper) 2) atTop (𝓝 u.val) :=
  exists_compact_graphShear_strong_h2_approximation (graphCoordinateSide_isOpen r hψ.continuous upper)
    r ψ hψ hC htrans hB upper (graphCoordinateSide_preimage r ψ hψ.continuous htrans upper) hK u hu

end Carleman
