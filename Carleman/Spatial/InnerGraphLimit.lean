module
public import Carleman.Spatial.DirichletExhaustionStrong
public import Carleman.Spatial.SubdomainLpLimit
public import Carleman.Spatial.DirichletCommutatorIdentity
public import Carleman.Continuous.RegularTimeCore
/-! Actual inner-domain operator graphs approximating every original graph coefficient. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_exhaustion_graph_approximation (hS : IsOpen S) (hd : 0<d)
    (hb : Bornology.IsBounded S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n, T n⊆S)
    (hm : Monotone T) (hcover : S⊆⋃ n, T n) :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    let Bn := fun n => (boundedDirichletOriginalForm (hT n) hd (hb.subset (hTS n))).model
    ∀ z : B.operatorGraph, ∃ Z : ∀ n, (Bn n).operatorGraph,
      (∀ n, (Bn n).graphA (Z n)=subdomainLp (hTS n) (B.graphA z)) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet ((Bn n).graphH (Z n)))
        atTop (𝓝 (B.graphH z)) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet
        (WeakSobolevJet.field 1 (dirichletDomainJet (hT n) hd (hb.subset (hTS n)) ((Bn n).graphDomain (Z n)))))
        atTop (𝓝 (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain z)))) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet ((Bn n).graphA (Z n)))
        atTop (𝓝 (B.graphA z)) := by
  intro B Bn z
  let zn (n : ℕ) := (Bn n).resolvent 0 le_rfl (subdomainLp (hTS n) (B.graphA z))
  let Z (n : ℕ) := (Bn n).graphOfDomain (zn n)
  have hzn (n : ℕ) : (Bn n).operator (zn n)=subdomainLp (hTS n) (B.graphA z) := by
    simpa only [zero_smul,add_zero] using (Bn n).resolvent_equation 0 le_rfl (subdomainLp (hTS n) (B.graphA z))
  have hZ (n : ℕ) : (Bn n).graphA (Z n)=subdomainLp (hTS n) (B.graphA z) := hzn n
  let u := dirichletDomainJet hS hd hb (B.graphDomain z)
  let v (n : ℕ) := dirichletDomainJet (hT n) hd (hb.subset (hTS n)) (zn n)
  have hu : u∈dirichletJetSpace S := (dirichletDomainJet_graph hS hd hb (B.graphDomain z)).1
  have huf : IsWeakNegativeLaplacian u (B.graphA z) := by
    have hh := (dirichletDomainJet_graph hS hd hb (B.graphDomain z)).2
    rwa [B.graphDomain_operator] at hh
  have hv (n : ℕ) : v n∈dirichletJetSpace (T n) :=
    (dirichletDomainJet_graph (hT n) hd (hb.subset (hTS n)) (zn n)).1
  have hvf (n : ℕ) : IsWeakNegativeLaplacian (v n) (subdomainLp (hTS n) (B.graphA z)) := by
    have hh := (dirichletDomainJet_graph (hT n) hd (hb.subset (hTS n)) (zn n)).2
    rwa [hzn n] at hh
  have hZD (n : ℕ) : (Bn n).graphDomain (Z n)=zn n := Subtype.ext rfl
  have hZH (n : ℕ) : (Bn n).graphH (Z n)=(zn n : Lp ℝ 2 (volume.restrict (T n))) := rfl
  have hzH : B.graphH z=(B.graphDomain z : Lp ℝ 2 (volume.restrict S)) := rfl
  have ht := dirichlet_exhaustion_strong_H1 hS hd hb u hu (B.graphA z) huf T hT hTS hm hcover v hv hvf
  refine ⟨Z,hZ,?_,?_,?_⟩
  · have hh := (WeakSobolevJet.valueCLM.continuous.tendsto u).comp ht
    simpa only [Function.comp_def,WeakSobolevJet.valueCLM_apply,WeakSobolevJet.extendDirichlet_value,
      v,u,dirichletDomainJet_value,subdomainZeroExtend,hZH,hzH] using hh
  · have hh := ((WeakSobolevJet.fieldCLM 1).continuous.tendsto u).comp ht
    simpa only [Function.comp_def,WeakSobolevJet.fieldCLM_apply,WeakSobolevJet.extendDirichlet_field,hZD,v,u] using hh
  · simp only [hZ]
    exact subdomainZeroExtend_restrict_tendsto_of_exhaustion hS.measurableSet T
      (fun n => (hT n).measurableSet) hTS hm hcover (B.graphA z)

theorem exists_halfspaceSmoothInner_graph_approximation {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) (N : ℕ) :
    let S := {x | ∀ i, b i<ℓ i x}
    let hS := finite_halfspace_isOpen ℓ b
    let hT := fun n => halfspaceSmoothInner_open ℓ b (N+n)
    let hTS := fun n => subset_closure.trans (halfspaceSmoothInner_closure_subset ℓ b (N+n))
    let B := (boundedDirichletOriginalForm hS hd hb).model
    let Bn := fun n => (boundedDirichletOriginalForm (hT n) hd (hb.subset (hTS n))).model
    ∀ z : B.operatorGraph, ∃ Z : ∀ n, (Bn n).operatorGraph,
      (∀ n, (Bn n).graphA (Z n)=subdomainLp (hTS n) (B.graphA z)) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet ((Bn n).graphH (Z n)))
        atTop (𝓝 (B.graphH z)) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet
        (WeakSobolevJet.field 1 (dirichletDomainJet (hT n) hd (hb.subset (hTS n)) ((Bn n).graphDomain (Z n)))))
        atTop (𝓝 (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain z)))) ∧
      Tendsto (fun n => subdomainZeroExtend S (hT n).measurableSet ((Bn n).graphA (Z n)))
        atTop (𝓝 (B.graphA z)) := by
  intro S hS hT hTS B Bn
  let T := fun n => halfspaceSmoothInner ℓ b (N+n)
  have hm : Monotone T := fun n m hnm => halfspaceSmoothInner_mono ℓ b (Nat.add_le_add_left hnm N)
  have hcover : S⊆⋃ n, T n := by
    intro x hx
    obtain ⟨n,hn⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hx).exists
    exact mem_iUnion.mpr ⟨n,halfspaceSmoothInner_mono ℓ b (Nat.le_add_left n N) hn⟩
  exact exists_dirichlet_exhaustion_graph_approximation hS hd hb T hT hTS hm hcover

end Carleman
