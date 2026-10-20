module
public import Carleman.Spatial.StrongH2GraphTransport
public import Carleman.Spatial.BoxStrongH2Density
public import Carleman.Spatial.BoundaryCutoffTransfer
public import Carleman.Spatial.FiniteLocalH2Gluing
/-! Full H²∩H¹₀ topology and actual continuous boundary cutoff transfer.
Target H² membership comes from the original localized weak equation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d m n : ℕ} {S T : Set (SpatialCoordinates d)}

def WeakSobolevJet.truncateCLM (h : m≤n) :
    WeakSobolevJet d n (volume.restrict S) S →L[ℝ] WeakSobolevJet d m (volume.restrict S) S :=
  (truncate h).mkContinuous 1 (fun u => by simpa only [one_mul] using norm_truncate_le h u)

def dirichletH2JetSpace (S : Set (SpatialCoordinates d)) :
    Submodule ℝ (WeakSobolevJet d 2 (volume.restrict S) S) :=
  (dirichletJetSpace S).comap (WeakSobolevJet.truncate (by decide : 1≤2))

theorem dirichletH2JetSpace_isClosed (S : Set (SpatialCoordinates d)) :
    IsClosed (dirichletH2JetSpace S : Set (WeakSobolevJet d 2 (volume.restrict S) S)) :=
  (Submodule.isClosed_topologicalClosure _).preimage (WeakSobolevJet.truncateCLM (S := S) (by decide : 1≤2)).continuous

instance dirichletH2JetSpace_complete (S : Set (SpatialCoordinates d)) :
    CompleteSpace (dirichletH2JetSpace S) := by
  let : IsClosed (dirichletH2JetSpace S : Set (WeakSobolevJet d 2 (volume.restrict S) S)) := dirichletH2JetSpace_isClosed S
  exact IsClosed.completeSpace_coe

def dirichletH2ValueCLM (S : Set (SpatialCoordinates d)) :
    dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
  WeakSobolevJet.valueCLM.comp (dirichletH2JetSpace S).subtypeL

def dirichletH2LiftLinear (hT : IsOpen T)
    (P : dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u, ∃ v : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.value v=P u) :
    dirichletH2JetSpace S →ₗ[ℝ] WeakSobolevJet d 2 (volume.restrict T) T where
  toFun u := (hl u).choose
  map_add' u v := by
    apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
    change WeakSobolevJet.value ((hl (u+v)).choose)=WeakSobolevJet.value ((hl u).choose+(hl v).choose)
    calc
      _ = P (u+v) := (hl (u+v)).choose_spec
      _ = P u+P v := P.map_add u v
      _ = WeakSobolevJet.value ((hl u).choose)+WeakSobolevJet.value ((hl v).choose) :=
        congrArg₂ (·+·) (hl u).choose_spec.symm (hl v).choose_spec.symm
      _ = _ := (map_add WeakSobolevJet.value _ _).symm
  map_smul' c u := by
    apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
    change WeakSobolevJet.value ((hl (c • u)).choose)=WeakSobolevJet.value (c • (hl u).choose)
    calc
      _ = P (c • u) := (hl (c • u)).choose_spec
      _ = c • P u := P.map_smul c u
      _ = c • WeakSobolevJet.value ((hl u).choose) := congrArg (c • ·) (hl u).choose_spec.symm
      _ = _ := (map_smul WeakSobolevJet.value c _).symm

theorem dirichletH2LiftLinear_value (hT : IsOpen T)
    (P : dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u, ∃ v : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.value v=P u)
    (u : dirichletH2JetSpace S) : WeakSobolevJet.value (dirichletH2LiftLinear (S := S) hT P hl u)=P u :=
  (hl u).choose_spec

theorem dirichletH2LiftLinear_closedGraph (hT : IsOpen T)
    (P : dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u, ∃ v : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.value v=P u) :
    IsClosed ((dirichletH2LiftLinear (S := S) hT P hl).graph : Set
      (dirichletH2JetSpace S × WeakSobolevJet d 2 (volume.restrict T) T)) := by
  have he : ((dirichletH2LiftLinear (S := S) hT P hl).graph : Set
      (dirichletH2JetSpace S × WeakSobolevJet d 2 (volume.restrict T) T))=
      {p | WeakSobolevJet.value p.2=P p.1} := by
    ext ⟨u,v⟩
    change v=dirichletH2LiftLinear (S := S) hT P hl u ↔ WeakSobolevJet.value v=P u
    constructor
    · rintro rfl
      exact dirichletH2LiftLinear_value (S := S) hT P hl u
    · intro hv
      apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
      rw [dirichletH2LiftLinear_value,hv]
  rw [he]
  exact isClosed_eq (WeakSobolevJet.valueCLM.continuous.comp continuous_snd)
    (P.continuous.comp continuous_fst)

def dirichletH2LiftCLM (hT : IsOpen T)
    (P : dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u, ∃ v : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.value v=P u) :
    dirichletH2JetSpace S →L[ℝ] WeakSobolevJet d 2 (volume.restrict T) T := by
  letI : CompleteSpace (dirichletH2JetSpace S) := dirichletH2JetSpace_complete S
  exact ContinuousLinearMap.ofIsClosedGraph (E := dirichletH2JetSpace S)
    (F := WeakSobolevJet d 2 (volume.restrict T) T) (g := dirichletH2LiftLinear (S := S) hT P hl)
    (dirichletH2LiftLinear_closedGraph (S := S) hT P hl)

theorem dirichletH2LiftCLM_value (hT : IsOpen T)
    (P : dirichletH2JetSpace S →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u, ∃ v : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.value v=P u)
    (u : dirichletH2JetSpace S) : WeakSobolevJet.value (dirichletH2LiftCLM (S := S) hT P hl u)=P u :=
  dirichletH2LiftLinear_value (S := S) hT P hl u

def DirichletH2Regular (T : Set (SpatialCoordinates d)) : Prop :=
  ∀ v : WeakSobolevJet d 1 (volume.restrict T) T, v∈dirichletJetSpace T →
    ∀ g : Lp ℝ 2 (volume.restrict T), IsWeakNegativeLaplacian v g →
      ∃ V : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.truncate (by decide : 1≤2) V=v

theorem dirichletH2Regular_box (a b : Fin d → ℝ) (hpos : ∀ i, a i<b i) :
    DirichletH2Regular (openCoordinateBox a b) := by
  obtain ⟨_,_,hr⟩ := exists_box_dirichlet_H2_bound a b hpos
  intro u hu f hf
  obtain ⟨U,hU,_,_⟩ := hr u hu f hf
  exact ⟨U,hU⟩

theorem dirichletH2Regular_graphEpigraph
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value) :
    DirichletH2Regular {x | ψ x<x r} :=
  exists_graphEpigraph_dirichlet_H2 r ψ hψ hC htrans hB

theorem dirichletH2Regular_graphHypograph
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value) :
    DirichletH2Regular {x | x r<ψ x} :=
  exists_graphHypograph_dirichlet_H2 r ψ hψ hC htrans hB

theorem dirichletH2Regular_smoothInner {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {z : SpatialCoordinates d} (hz : z∈halfspaceSmoothInner ℓ b n) :
    DirichletH2Regular (halfspaceSmoothInner ℓ b n) := by
  intro u hu f hf
  obtain ⟨U,hU,_⟩ := halfspaceSmoothInner_dirichlet_H2 ℓ b n hb hz u hu f hf
  exact ⟨U,hU⟩

namespace SpatialTest

def cutoffValueTransfer (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S T : Set (SpatialCoordinates d)) : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T) :=
  (η.valueMultiplier (volume.restrict T)).continuousLinearMap.comp
    ((Physical.restrictRegionCLM T).comp (Physical.restrictRegionCLM S).adjoint)

theorem cutoffValueTransfer_apply (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (u : Lp ℝ 2 (volume.restrict S)) :
    η.cutoffValueTransfer S T u=(η.valueMultiplier (volume.restrict T)).map
      (subdomainZeroExtend T hS.measurableSet u) := by
  simp only [cutoffValueTransfer,ContinuousLinearMap.comp_apply,Physical.restrictRegion_adjoint S hS.measurableSet]
  rfl

theorem cutoffH2_value_exists (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    ∃ V : WeakSobolevJet d 2 (volume.restrict T) T,
      WeakSobolevJet.value V=η.cutoffValueTransfer S T (WeakSobolevJet.value u.val) := by
  let v := WeakSobolevJet.truncate (by decide : 1≤2) u.val
  have hv : v∈dirichletJetSpace S := u.property
  obtain ⟨V,hV⟩ := hreg (η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS v hv))
    (η.cutoff_extendDirichlet_mem hS hT hST v hv) (η.cutoffTransferredLoad hS v hv (negativeLaplacian u.val))
    (η.cutoff_extendDirichlet_equation hS hT hTS v hv _ (negativeLaplacian_test u.val))
  refine ⟨V,?_⟩
  have he := congrArg WeakSobolevJet.value hV
  rw [WeakSobolevJet.truncate_value,cutoffWeakJet_value,WeakSobolevJet.extendDirichlet_value] at he
  rw [cutoffValueTransfer_apply η hS]
  exact he

def cutoffH2Transfer (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) :
    dirichletH2JetSpace S →L[ℝ] WeakSobolevJet d 2 (volume.restrict T) T :=
  dirichletH2LiftCLM hT ((η.cutoffValueTransfer S T).comp (dirichletH2ValueCLM S))
    (η.cutoffH2_value_exists hS hT hST hTS hreg)

theorem cutoffH2Transfer_value (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    WeakSobolevJet.value (η.cutoffH2Transfer hS hT hST hTS hreg u)=
      η.cutoffValueTransfer S T (WeakSobolevJet.value u.val) :=
  dirichletH2LiftCLM_value _ _ _ _

theorem cutoffH2Transfer_truncate (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    WeakSobolevJet.truncate (by decide : 1≤2) (η.cutoffH2Transfer hS hT hST hTS hreg u)=
      η.cutoffWeakJet hT (WeakSobolevJet.extendDirichlet T hS
        (WeakSobolevJet.truncate (by decide : 1≤2) u.val) u.property) := by
  apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [WeakSobolevJet.truncate_value,cutoffH2Transfer_value,cutoffValueTransfer_apply η hS,
    cutoffWeakJet_value]
  exact congrArg (η.valueMultiplier (volume.restrict T)).map
    (WeakSobolevJet.extendDirichlet_value hS
      (WeakSobolevJet.truncate (by decide : 1≤2) u.val) u.property).symm

theorem cutoffH2Transfer_dirichlet (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    WeakSobolevJet.truncate (by decide : 1≤2) (η.cutoffH2Transfer hS hT hST hTS hreg u)∈dirichletJetSpace T := by
  rw [cutoffH2Transfer_truncate]
  exact η.cutoff_extendDirichlet_mem hS hT hST _ u.property

theorem cutoffH2Transfer_tendsto (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (U : ℕ → WeakSobolevJet d 2 (volume.restrict S) S)
    (hU : ∀ n, U n∈dirichletH2JetSpace S) (u : dirichletH2JetSpace S)
    (ht : Tendsto U atTop (𝓝 u.val)) :
    Tendsto (fun n => η.cutoffH2Transfer hS hT hST hTS hreg ⟨U n,hU n⟩) atTop
      (𝓝 (η.cutoffH2Transfer hS hT hST hTS hreg u)) :=
  ((η.cutoffH2Transfer hS hT hST hTS hreg).continuous.tendsto u).comp (tendsto_subtype_rng.mpr ht)

theorem cutoffH2Transfer_ae (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    WeakSobolevJet.value (η.cutoffH2Transfer hS hT hST hTS hreg u) =ᵐ[volume.restrict T]
      (fun x => η.value x*S.indicator (WeakSobolevJet.value u.val) x) := by
  rw [cutoffH2Transfer_value,cutoffValueTransfer_apply η hS]
  filter_upwards [(η.valueMultiplier (volume.restrict T)).map_ae
      (subdomainZeroExtend T hS.measurableSet (WeakSobolevJet.value u.val)),
    subdomainZeroExtend_ae (S := T) hS.measurableSet (WeakSobolevJet.value u.val)] with x hm hz
  rw [hm,hz]
  rfl

theorem cutoffH2Transfer_of_smooth (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S)
    (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hu : WeakSobolevJet.value u.val =ᵐ[volume.restrict S] φ.value) :
    η.cutoffH2Transfer hS hT hST hTS hreg u=(η.mulSmooth φ.smooth).allOrderJetOn T 2 := by
  apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [allOrderJetOn_value]
  apply Lp.ext
  have he := ((ae_restrict_iff' hS.measurableSet).mp hu).filter_mono (ae_restrict_le (s := T))
  filter_upwards [η.cutoffH2Transfer_ae hS hT hST hTS hreg u,he,
    (η.mulSmooth φ.smooth).toLp_ae (volume.restrict T),ae_restrict_mem hT.measurableSet]
    with x hv hu hp hxT
  rw [hv,hp]
  change η.value x*S.indicator (WeakSobolevJet.value u.val) x=η.value x*φ.value x
  by_cases hη : η.value x=0
  · simp only [hη,zero_mul]
  · have hxS := hTS ⟨hxT,subset_tsupport _ hη⟩
    rw [indicator_of_mem hxS,hu hxS]

theorem frontier_mem_of_cutoff_agreement (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    {x : SpatialCoordinates d} (hx : x∈frontier T) (hη : η.value x≠0) : x∈frontier S := by
  let N := {x | η.value x≠0}
  have hN : IsOpen N := isOpen_ne.preimage η.smooth.continuous
  have he : S∩N=T∩N := by
    ext y
    constructor
    · rintro ⟨hy,hn⟩
      exact ⟨hST ⟨hy,subset_tsupport _ hn⟩,hn⟩
    · rintro ⟨hy,hn⟩
      exact ⟨hTS ⟨hy,subset_tsupport _ hn⟩,hn⟩
  have hf : frontier S∩N=frontier T∩N := by
    rw [← frontier_inter_open_inter hN,he,frontier_inter_open_inter hN]
  exact ((Set.ext_iff.mp hf x).mpr ⟨hx,hη⟩).1

theorem cutoffTransfer_boundary_zero (η φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hφ : ∀ x∈frontier S, φ.value x=0) :
    ∀ x∈frontier T, (η.mulSmooth φ.smooth).value x=0 := by
  intro x hx
  change η.value x*φ.value x=0
  by_cases hη : η.value x=0
  · rw [hη,zero_mul]
  · rw [hφ x (η.frontier_mem_of_cutoff_agreement hST hTS hx hη),mul_zero]

theorem exists_cutoff_box_strong_h2_approximation
    (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (a b : Fin d → ℝ) (hpos : ∀ i, a i<b i) (hT : IsOpen T)
    (hST : openCoordinateBox a b∩tsupport η.value⊆T)
    (hTS : T∩tsupport η.value⊆openCoordinateBox a b) (hreg : DirichletH2Regular T)
    (u : dirichletH2JetSpace (openCoordinateBox a b)) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier T, (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2) ((U n).allOrderJetOn T 2)∈dirichletJetSpace T) ∧
      Tendsto (fun n => (U n).allOrderJetOn T 2) atTop
        (𝓝 (η.cutoffH2Transfer (openCoordinateBox_isOpen a b) hT hST hTS hreg u)) := by
  obtain ⟨F,hF,hD,ht⟩ := exists_box_dirichlet_strong_h2_approximation a b hpos u.val u.property
  let v (n : ℕ) : dirichletH2JetSpace (openCoordinateBox a b) := ⟨(F n).allOrderJetOn (openCoordinateBox a b) 2,hD n⟩
  have he (n : ℕ) : η.cutoffH2Transfer (openCoordinateBox_isOpen a b) hT hST hTS hreg (v n)=
      (η.mulSmooth (F n).smooth).allOrderJetOn T 2 := by
    apply η.cutoffH2Transfer_of_smooth (openCoordinateBox_isOpen a b) hT hST hTS hreg (v n) (F n)
    change WeakSobolevJet.value ((F n).allOrderJetOn (openCoordinateBox a b) 2) =ᵐ[_] _
    rw [allOrderJetOn_value]
    exact (F n).toLp_ae _
  refine ⟨fun n => η.mulSmooth (F n).smooth,fun n => η.cutoffTransfer_boundary_zero (F n) hST hTS (hF n),?_,?_⟩
  · intro n
    rw [← he n]
    exact η.cutoffH2Transfer_dirichlet (openCoordinateBox_isOpen a b) hT hST hTS hreg (v n)
  · have hc := η.cutoffH2Transfer_tendsto (openCoordinateBox_isOpen a b) hT hST hTS hreg
      (fun n => (F n).allOrderJetOn (openCoordinateBox a b) 2) hD u ht
    simpa only [← he] using hc

end SpatialTest
end Carleman
