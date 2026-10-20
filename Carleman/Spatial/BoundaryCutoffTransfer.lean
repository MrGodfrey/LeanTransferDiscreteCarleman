module
public import Carleman.Spatial.GraphDomainRegularity
public import Carleman.Spatial.WeakLaplacianProduct
public import Carleman.Spatial.MollifiedProductTests
public import Carleman.Spatial.DirichletExtensionPairing
/-! Boundary-crossing cutoffs transfer the original H¹₀ state and full weak
Poisson equation between domains agreeing near the cutoff. The resulting
local H² jet restricts to the same original weak state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
namespace SpatialTest

def retarget (φ : SpatialTest S) (hT : tsupport φ.value ⊆ T) : SpatialTest T :=
  ⟨φ.value,φ.smooth,φ.compact,hT⟩

theorem retarget_fullJet (φ : SpatialTest S) (hT : tsupport φ.value ⊆ T) :
    (φ.retarget hT).fullJet=φ.fullJet := rfl

theorem extendDirichlet_pairing_of_support (hS : IsOpen S) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (φ : SpatialTest T) (hφ : tsupport φ.value ⊆ S) :
    weakGradientPairing (WeakSobolevJet.extendDirichlet T hS u hu) φ.sobolevJet=
      weakGradientPairing u (φ.retarget hφ).sobolevJet := by
  let χ := φ.retarget hφ
  calc
    _ = weakGradientPairing (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet :=
      (φ.fullJet_pairing hT _).symm
    _ = weakGradientPairing (WeakSobolevJet.zeroExtendDirichlet hS u hu) χ.fullJet := rfl
    _ = weakGradientPairing u (WeakSobolevJet.restrictDomain S χ.fullJet) :=
      WeakSobolevJet.zeroExtendDirichlet_pairing hS u hu χ.fullJet
    _ = _ := congrArg (weakGradientPairing u) (χ.fullJet_restrict hS)

theorem subdomainZeroExtend_inner_of_support (hS : IsOpen S) (hT : IsOpen T)
    (f : Lp ℝ 2 (volume.restrict S)) (φ : SpatialTest T) (hφ : tsupport φ.value ⊆ S) :
    inner ℝ (subdomainZeroExtend T hS.measurableSet f) (φ.toLp (volume.restrict T))=
      inner ℝ f ((φ.retarget hφ).toLp (volume.restrict S)) := by
  change inner ℝ (Physical.restrictRegionLp T (zeroExtendLp hS.measurableSet f)) _=_
  rw [← φ.fullJet_inner hT,← retarget_fullJet φ hφ,zeroExtendLp_inner]
  rw [← WeakSobolevJet.restrictDomain_value,(φ.retarget hφ).fullJet_restrict hS,SpatialTest.sobolevJet_value]

def cutoffWeakJet (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hT : IsOpen T) :
    WeakSobolevJet d 1 (volume.restrict T) T →L[ℝ] WeakSobolevJet d 1 (volume.restrict T) T :=
  weakFirstProductCLM hT (ae_restrict_mem hT.measurableSet) (η.valueMultiplier (volume.restrict T))
    (fun i => (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T))
    η.smooth.contDiffOn (fun _ => Eventually.of_forall fun _ => rfl)

theorem cutoffWeakJet_value (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    WeakSobolevJet.value (η.cutoffWeakJet hT u)=(η.valueMultiplier (volume.restrict T)).map (WeakSobolevJet.value u) := by
  unfold cutoffWeakJet
  exact weakFirstProduct_value hT (ae_restrict_mem hT.measurableSet) _ _ η.smooth.contDiffOn
    (fun _ => Eventually.of_forall fun _ => rfl) u

theorem cutoffWeakJet_gradient (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (η.cutoffWeakJet hT u))=
      (η.valueMultiplier (volume.restrict T)).map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        ((η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T)).map (WeakSobolevJet.value u) := by
  unfold cutoffWeakJet
  exact weakFirstProduct_component hT (ae_restrict_mem hT.measurableSet) _ _ η.smooth.contDiffOn
    (fun _ => Eventually.of_forall fun _ => rfl) u i

def cutoffTransfer (η : SpatialTest (univ : Set (SpatialCoordinates d))) (φ : SpatialTest S)
    (hST : S ∩ tsupport η.value ⊆ T) : SpatialTest T where
  value x := η.value x*φ.value x
  smooth := η.smooth.mul φ.smooth
  compact := φ.compact.mul_left
  support := fun _x hx => hST ⟨φ.support (tsupport_mul_subset_right hx),tsupport_mul_subset_left hx⟩

theorem cutoff_extendDirichlet_test (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S ∩ tsupport η.value ⊆ T) (φ : SpatialTest S) :
    η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS φ.sobolevJet (test_mem_dirichletJetSpace S φ))=
      (η.cutoffTransfer φ hST).sobolevJet := by
  apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [cutoffWeakJet_value,WeakSobolevJet.extendDirichlet_value,(η.cutoffTransfer φ hST).sobolevJet_value]
  apply Lp.ext
  filter_upwards [(η.valueMultiplier (volume.restrict T)).map_ae
      (Physical.restrictRegionLp T (zeroExtendLp hS.measurableSet (WeakSobolevJet.value φ.sobolevJet))),
    Physical.restrictRegionLp_ae T (zeroExtendLp hS.measurableSet (WeakSobolevJet.value φ.sobolevJet)),
    (φ.zeroExtendDirichlet_value_ae hS).filter_mono ae_restrict_le,
    (η.cutoffTransfer φ hST).toLp_ae (volume.restrict T)] with x hm hr hz ht
  rw [hm,hr,ht]
  change η.value x*(zeroExtendLp hS.measurableSet (WeakSobolevJet.value φ.sobolevJet) x)=η.value x*φ.value x
  rw [← WeakSobolevJet.zeroExtendDirichlet_value hS φ.sobolevJet (test_mem_dirichletJetSpace S φ),hz]

theorem cutoff_extendDirichlet_mem (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S ∩ tsupport η.value ⊆ T)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS u hu) ∈ dirichletJetSpace T := by
  obtain ⟨U,hU,ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using fun n => exists_test_of_mem_test_span hS (hU n)
  have hu' (n : ℕ) : U n ∈ dirichletJetSpace S := Submodule.le_topologicalClosure _ (hU n)
  have he := WeakSobolevJet.restrictDomain_tendsto (S := T) (WeakSobolevJet.zeroExtendDirichlet_tendsto hS U hu' u hu ht)
  have hp := ((η.cutoffWeakJet hT).continuous.tendsto (WeakSobolevJet.extendDirichlet T hS u hu)).comp he
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hp
  apply Eventually.of_forall
  intro n
  change η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS (U n) (hu' n)) ∈ dirichletJetSpace T
  simp only [← hφ n,cutoff_extendDirichlet_test η hS hT hST]
  exact test_mem_dirichletJetSpace T _


def cutoffTransferredLoad (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) : Lp ℝ 2 (volume.restrict T) :=
  let v := WeakSobolevJet.extendDirichlet T hS u hu
  (η.valueMultiplier (volume.restrict T)).map (subdomainZeroExtend T hS.measurableSet f)-
    ∑ i : Fin d, ((2 : ℝ) • ((η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T)).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v))+
      (((η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T)).map
        (WeakSobolevJet.value v))

theorem cutoff_extendDirichlet_equation (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hTS : T ∩ tsupport η.value ⊆ S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    IsWeakNegativeLaplacian (η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS u hu))
      (η.cutoffTransferredLoad hS u hu f) := by
  let v := WeakSobolevJet.extendDirichlet T hS u hu
  let w := η.valueMultiplier (volume.restrict T)
  let dw i := (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T)
  let ddw i := ((η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).valueMultiplier (volume.restrict T)
  let g := subdomainZeroExtend T hS.measurableSet f
  have hdw (i) : (dw i).value =ᵐ[volume.restrict T] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := Eventually.of_forall fun _ => rfl
  have hddw (i) : (ddw i).value =ᵐ[volume.restrict T] (fun x => fderiv ℝ (dw i).value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := Eventually.of_forall fun _ => rfl
  intro φ
  let χ := φ.mulOn hT η.smooth.contDiffOn
  have hχ : tsupport χ.value ⊆ S := by
    intro x hx
    exact hTS ⟨φ.support (tsupport_mul_subset_right hx),tsupport_mul_subset_left hx⟩
  have he : weakGradientPairing v χ.sobolevJet=inner ℝ g (χ.toLp (volume.restrict T)) := by
    rw [extendDirichlet_pairing_of_support hS hT u hu χ hχ,hf (χ.retarget hχ)]
    exact (subdomainZeroExtend_inner_of_support hS hT f χ hχ).symm
  change weakGradientPairing (weakFirstProduct hT (ae_restrict_mem hT.measurableSet) w dw η.smooth.contDiffOn hdw v) φ.sobolevJet=
    inner ℝ (w.map g-∑ i : Fin d, ((2 : ℝ) • (dw i).map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v))+
      (ddw i).map (WeakSobolevJet.value v))) (φ.toLp (volume.restrict T))
  rw [weakGradientPairing_product_test hT w dw ddw η.smooth.contDiffOn
    (fun i => (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).smooth.contDiffOn) hdw hddw,he]
  dsimp only [χ]
  rw [SpatialTest.mulOn_toLp φ hT w η.smooth.contDiffOn,inner_sub_left,sum_inner,w.inner_map_left]

theorem cutoff_extendDirichlet_value_ae (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    WeakSobolevJet.value (η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS u hu)) =ᵐ[volume.restrict T]
      (fun x => η.value x*(S.indicator (WeakSobolevJet.value u) x)) := by
  rw [cutoffWeakJet_value,WeakSobolevJet.extendDirichlet_value]
  change (η.valueMultiplier (volume.restrict T)).map (subdomainZeroExtend T hS.measurableSet (WeakSobolevJet.value u)) =ᵐ[volume.restrict T] _
  filter_upwards [(η.valueMultiplier (volume.restrict T)).map_ae (subdomainZeroExtend T hS.measurableSet (WeakSobolevJet.value u)),
    subdomainZeroExtend_ae (S := T) hS.measurableSet (WeakSobolevJet.value u)] with x hm he
  rw [hm,he]
  rfl



theorem exists_local_H2_of_cutoff_transfer {R : Set (SpatialCoordinates d)}
    (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hR : IsOpen R)
    (hST : S ∩ tsupport η.value ⊆ T) (hTS : T ∩ tsupport η.value ⊆ S)
    (hRS : R ⊆ S) (hRT : R ⊆ T) (hη : ∀ x ∈ R, η.value x=1)
    (hreg : ∀ v : WeakSobolevJet d 1 (volume.restrict T) T, v ∈ dirichletJetSpace T →
      ∀ g : Lp ℝ 2 (volume.restrict T), IsWeakNegativeLaplacian v g →
        ∃ V : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.truncate (by omega : 1 ≤ 2) V=v)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict R) R,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain hRS u := by
  let v := η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS u hu)
  obtain ⟨V,hV⟩ := hreg v (η.cutoff_extendDirichlet_mem hS hT hST u hu)
    (η.cutoffTransferredLoad hS u hu f) (η.cutoff_extendDirichlet_equation hS hT hTS u hu f hf)
  refine ⟨WeakSobolevJet.restrictSubdomain hRT V,?_⟩
  apply WeakSobolevJet.value_injective hR (ae_restrict_mem hR.measurableSet)
  change WeakSobolevJet.value (WeakSobolevJet.restrictSubdomain hRT V)=_
  rw [WeakSobolevJet.restrictSubdomain_value,WeakSobolevJet.restrictSubdomain_value]
  have hv := congrArg WeakSobolevJet.value hV
  change WeakSobolevJet.value V=WeakSobolevJet.value v at hv
  rw [hv]
  apply Lp.ext
  filter_upwards [subdomainLp_ae hRT (WeakSobolevJet.value v),subdomainLp_ae hRS (WeakSobolevJet.value u),
    (η.cutoff_extendDirichlet_value_ae hS hT u hu).filter_mono (ae_mono (Measure.restrict_mono hRT le_rfl)),
    ae_restrict_mem hR.measurableSet] with x ht hs hx hr
  rw [ht,hs,hx,hη x hr,one_mul,indicator_of_mem (hRS hr)]



theorem exists_local_H2_of_cutoff_graph_epigraph {R : Set (SpatialCoordinates d)}
    (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hS : IsOpen S) (hR : IsOpen R)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (hST : S ∩ tsupport η.value ⊆ {x | ψ x < x r})
    (hTS : {x | ψ x < x r} ∩ tsupport η.value ⊆ S)
    (hRS : R ⊆ S) (hRT : R ⊆ {x | ψ x < x r}) (hη : ∀ x ∈ R, η.value x=1)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict R) R,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain hRS u := by
  exact exists_local_H2_of_cutoff_transfer η hS
    (isOpen_lt hψ.continuous (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)) hR hST hTS hRS hRT hη
    (fun v hv g hg => exists_graphEpigraph_dirichlet_H2 r ψ hψ hC htrans hB v hv g hg) u hu f hf


theorem exists_local_H2_of_cutoff_graph_hypograph {R : Set (SpatialCoordinates d)}
    (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hS : IsOpen S) (hR : IsOpen R)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (hST : S ∩ tsupport η.value ⊆ {x | x r < ψ x})
    (hTS : {x | x r < ψ x} ∩ tsupport η.value ⊆ S)
    (hRS : R ⊆ S) (hRT : R ⊆ {x | x r < ψ x}) (hη : ∀ x ∈ R, η.value x=1)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict R) R,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain hRS u := by
  exact exists_local_H2_of_cutoff_transfer η hS
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r) hψ.continuous) hR hST hTS hRS hRT hη
    (fun v hv g hg => exists_graphHypograph_dirichlet_H2 r ψ hψ hC htrans hB v hv g hg) u hu f hf


end SpatialTest
end Carleman
