module
public import Carleman.Spatial.CompactGraphDensity
/-! True nested cutoff localization and finite smooth partitions give strong
H² zero-boundary approximation on the original regular smooth inner domains. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff BigOperators
namespace Carleman
variable {d : ℕ} {S T V : Set (SpatialCoordinates d)}

def HasSmoothDirichletH2Approximation (u : WeakSobolevJet d 2 (volume.restrict S) S) : Prop :=
  ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
    (∀ n, ∀ x∈frontier S, (U n).value x=0) ∧
    (∀ n, WeakSobolevJet.truncate (by decide : 1≤2) ((U n).allOrderJetOn S 2)∈dirichletJetSpace S) ∧
    Tendsto (fun n => (U n).allOrderJetOn S 2) atTop (𝓝 u)

namespace SpatialTest

theorem cutoffH2Transfer_approximation (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S)
    (hu : HasSmoothDirichletH2Approximation u.val) :
    HasSmoothDirichletH2Approximation (η.cutoffH2Transfer hS hT hST hTS hreg u) := by
  obtain ⟨F,hF,hD,ht⟩ := hu
  let v (n : ℕ) : dirichletH2JetSpace S := ⟨(F n).allOrderJetOn S 2,hD n⟩
  have he (n : ℕ) : η.cutoffH2Transfer hS hT hST hTS hreg (v n)=
      (η.mulSmooth (F n).smooth).allOrderJetOn T 2 := by
    apply η.cutoffH2Transfer_of_smooth hS hT hST hTS hreg (v n) (F n)
    change WeakSobolevJet.value ((F n).allOrderJetOn S 2) =ᵐ[_] _
    rw [allOrderJetOn_value]
    exact (F n).toLp_ae _
  refine ⟨fun n => η.mulSmooth (F n).smooth,fun n => η.cutoffTransfer_boundary_zero (F n) hST hTS (hF n),?_,?_⟩
  · intro n
    rw [← he n]
    exact η.cutoffH2Transfer_dirichlet hS hT hST hTS hreg (v n)
  · have hc := η.cutoffH2Transfer_tendsto hS hT hST hTS hreg
      (fun n => (F n).allOrderJetOn S 2) hD u ht
    simpa only [← he] using hc

theorem cutoffH2Transfer_nested_roundtrip (η γ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T)
    (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hSTγ : S∩tsupport γ.value⊆T) (hTSγ : T∩tsupport γ.value⊆S)
    (hγ : ∀ x∈tsupport η.value, γ.value x=1)
    (hregS : DirichletH2Regular S) (hregT : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    γ.cutoffH2Transfer hT hS hTSγ hSTγ hregS
      ⟨η.cutoffH2Transfer hS hT hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS hT hST hTS hregT u⟩=
      η.cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  apply Lp.ext
  have hv := ((ae_restrict_iff' hT.measurableSet).mp (η.cutoffH2Transfer_ae hS hT hST hTS hregT u)).filter_mono
    (ae_restrict_le (s := S))
  filter_upwards [γ.cutoffH2Transfer_ae hT hS hTSγ hSTγ hregS
    ⟨η.cutoffH2Transfer hS hT hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS hT hST hTS hregT u⟩,
    hv,η.cutoffH2Transfer_ae hS hS inter_subset_left inter_subset_left hregS u,
    ae_restrict_mem hS.measurableSet] with x ho hi hs hxS
  have hzS : S.indicator (WeakSobolevJet.value u.val) x=WeakSobolevJet.value u.val x := indicator_of_mem hxS _
  have hprod : γ.value x*η.value x=η.value x := by
    by_cases hη : η.value x=0
    · rw [hη,mul_zero]
    · rw [hγ x (subset_tsupport _ hη),one_mul]
  apply ho.trans
  apply Eq.trans _ (hs.trans (congrArg (fun t : ℝ => η.value x*t) hzS)).symm
  by_cases hxT : x∈T
  · rw [indicator_of_mem hxT]
    calc
      _ = γ.value x*(η.value x*WeakSobolevJet.value u.val x) :=
        congrArg (fun t : ℝ => γ.value x*t) ((hi hxT).trans (congrArg (fun t : ℝ => η.value x*t) hzS))
      _ = _ := by rw [← mul_assoc,hprod]
  · rw [indicator_of_notMem hxT,mul_zero]
    have hz : η.value x=0 := by
      by_contra hn
      exact hxT (hST ⟨hxS,subset_tsupport _ hn⟩)
    rw [hz,zero_mul]

theorem cutoffH2Transfer_off_support (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hreg : DirichletH2Regular T) (u : dirichletH2JetSpace S) :
    ∀ᵐ x ∂volume.restrict T, x∉tsupport η.value →
      WeakSobolevJet.value (η.cutoffH2Transfer hS hT hST hTS hreg u) x=0 := by
  filter_upwards [η.cutoffH2Transfer_ae hS hT hST hTS hreg u] with x hx
  intro hn
  rw [hx,image_eq_zero_of_notMem_tsupport hn,zero_mul]

end SpatialTest

theorem exists_localized_strong_h2_approximation
    (hS : IsOpen S) (hT : IsOpen T) (hV : IsOpen V)
    (he : ∀ x∈V, x∈S ↔ x∈T)
    (hregS : DirichletH2Regular S) (hregT : DirichletH2Regular T)
    (hdensity : ∀ (K : Set (SpatialCoordinates d)), IsCompact K → ∀ v : dirichletH2JetSpace T,
      (∀ᵐ x ∂volume.restrict T, x∉K → WeakSobolevJet.value v.val x=0) → HasSmoothDirichletH2Approximation v.val)
    (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hη : tsupport η.value⊆V)
    (u : dirichletH2JetSpace S) :
    HasSmoothDirichletH2Approximation (η.cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u) := by
  obtain ⟨γ,hγ⟩ := exists_spatialTest_eq_one_on_compact hV η.compact hη
  have hST : S∩tsupport η.value⊆T := fun x hx => (he x (hη hx.2)).mp hx.1
  have hTS : T∩tsupport η.value⊆S := fun x hx => (he x (hη hx.2)).mpr hx.1
  have hSTγ : S∩tsupport γ.toUniv.value⊆T := fun x hx => (he x (γ.support hx.2)).mp hx.1
  have hTSγ : T∩tsupport γ.toUniv.value⊆S := fun x hx => (he x (γ.support hx.2)).mpr hx.1
  let v : dirichletH2JetSpace T :=
    ⟨η.cutoffH2Transfer hS hT hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS hT hST hTS hregT u⟩
  have hv := hdensity (tsupport η.value) η.compact v (η.cutoffH2Transfer_off_support hS hT hST hTS hregT u)
  have hh := γ.toUniv.cutoffH2Transfer_approximation hT hS hTSγ hSTγ hregS v hv
  rwa [η.cutoffH2Transfer_nested_roundtrip γ.toUniv hS hT hST hTS hSTγ hTSγ hγ hregS hregT u] at hh

theorem compact_fullspace_hasSmoothDirichletH2Approximation (hd : 0<d)
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) (u : dirichletH2JetSpace (univ : Set (SpatialCoordinates d)))
    (hu : ∀ᵐ x ∂volume.restrict (univ : Set (SpatialCoordinates d)), x∉K → WeakSobolevJet.value u.val x=0) :
    HasSmoothDirichletH2Approximation u.val := by
  obtain ⟨a,b,η,hpos,hη,hs⟩ := exists_fullspace_box_cutoff hK
  exact exists_compact_localbox_strong_h2_approximation isOpen_univ
    (dirichletH2Regular_univ hd) η hη a b hpos (fun _ hx => hs hx.2) (subset_univ _) u hu

theorem dirichletH2Regular_graphSide (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (upper : Bool) : DirichletH2Regular (graphCoordinateSide r ψ upper) := by
  cases upper
  · exact dirichletH2Regular_graphHypograph r ψ hψ hC htrans hB
  · exact dirichletH2Regular_graphEpigraph r ψ hψ hC htrans hB

theorem exists_interior_local_strong_h2_approximation (hd : 0<d)
    (hS : IsOpen S) (hregS : DirichletH2Regular S) {c : SpatialCoordinates d} (hc : c∈S)
    (u : dirichletH2JetSpace S) :
    ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ c∈V ∧ Bornology.IsBounded V ∧
      ∀ η : SpatialTest (univ : Set (SpatialCoordinates d)), tsupport η.value⊆V →
        HasSmoothDirichletH2Approximation (η.cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hc)
  refine ⟨ball c δ,isOpen_ball,mem_ball_self hδ,isBounded_ball,?_⟩
  intro η hη
  exact exists_localized_strong_h2_approximation hS isOpen_univ isOpen_ball
    (fun x hx => ⟨fun _ => mem_univ _,fun _ => hball hx⟩) hregS (dirichletH2Regular_univ hd)
    (fun _ hk v hv => compact_fullspace_hasSmoothDirichletH2Approximation hd hk v hv) η hη u

theorem exists_boundary_local_strong_h2_approximation
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ω g) (a : ℝ)
    (hregS : DirichletH2Regular {x | g x<a}) (c : SpatialCoordinates d)
    (hc : g c=a) (hreg : fderiv ℝ g c≠0) (u : dirichletH2JetSpace {x | g x<a}) :
    ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ c∈V ∧ Bornology.IsBounded V ∧
      ∀ η : SpatialTest (univ : Set (SpatialCoordinates d)), tsupport η.value⊆V →
        HasSmoothDirichletH2Approximation
          (η.cutoffH2Transfer (isOpen_lt hg.continuous continuous_const) (isOpen_lt hg.continuous continuous_const)
            inter_subset_left inter_subset_left hregS u) := by
  obtain ⟨r,ψ,C,B,W,hW,hcW,hψ,hC,hB,htrans,hside⟩ := exists_sublevel_graph_near_regular g hg a c hc hreg
  have hex : ∃ upper : Bool, ∀ x∈W, x∈{x | g x<a} ↔ x∈graphCoordinateSide r ψ upper := by
    rcases hside with hh | hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨upper,he⟩ := hex
  have hB' : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value := hB
  let V := W∩ball c 1
  have hV : IsOpen V := hW.inter isOpen_ball
  refine ⟨V,hV,⟨hcW,mem_ball_self (by norm_num)⟩,isBounded_ball.subset inter_subset_right,?_⟩
  intro η hη
  exact exists_localized_strong_h2_approximation (isOpen_lt hg.continuous continuous_const)
    (graphCoordinateSide_isOpen r hψ.continuous upper) hV (fun x hx => he x hx.1) hregS
    (dirichletH2Regular_graphSide r ψ hψ hC htrans hB' upper)
    (fun _ hk v hv => exists_compact_graphSide_strong_h2_approximation r ψ hψ hC htrans hB' upper hk v hv) η hη u

namespace SpatialTest

def sumTest {ι : Type*} [Fintype ι] (F : ι → SpatialTest (univ : Set (SpatialCoordinates d))) :
    SpatialTest (univ : Set (SpatialCoordinates d)) where
  value := ∑ i, (F i).value
  smooth := by
    change ContDiff ℝ ∞ (fun x => (∑ i, (F i).value) x)
    simp_rw [Finset.sum_apply]
    exact ContDiff.sum (fun i _ => (F i).smooth)
  compact := HasCompactSupport.finset_sum (fun i (_ : i∈(Finset.univ : Finset ι)) => (F i).compact)
  support := subset_univ _

theorem sumTest_allOrderJetOn {ι : Type*} [Fintype ι] (hS : IsOpen S)
    (F : ι → SpatialTest (univ : Set (SpatialCoordinates d))) (m : ℕ) :
    (sumTest F).allOrderJetOn S m=∑ i, (F i).allOrderJetOn S m := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  simp only [map_sum,allOrderJetOn_value]
  apply Lp.ext
  have hae := eventuallyEq_sum (s := Finset.univ) (fun i _ => (F i).toLp_ae (volume.restrict S))
  filter_upwards [(sumTest F).toLp_ae (volume.restrict S),
    Lp.coeFn_finsetSum Finset.univ (fun i => (F i).toLp (volume.restrict S)),hae] with x hx hsum hvals
  rw [hx,hsum,hvals]
  rfl

theorem cutoffH2Transfer_partition {ι : Type*} [Fintype ι]
    (hS : IsOpen S) (hregS : DirichletH2Regular S)
    (η : ι → SpatialTest (univ : Set (SpatialCoordinates d)))
    (hsum : ∀ x∈S, ∑ i, (η i).value x=1) (u : dirichletH2JetSpace S) :
    (∑ i, (η i).cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u)=u.val := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [map_sum]
  apply Lp.ext
  have hae := eventuallyEq_sum (s := Finset.univ) (fun i _ =>
    (η i).cutoffH2Transfer_ae hS hS inter_subset_left inter_subset_left hregS u)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => WeakSobolevJet.value
      ((η i).cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u)),hae,
    ae_restrict_mem hS.measurableSet] with x hx hv hxS
  rw [hx,hv]
  simp only [Finset.sum_apply,indicator_of_mem hxS]
  rw [← Finset.sum_mul,hsum x hxS,one_mul]

end SpatialTest

theorem hasSmoothDirichletH2Approximation_sum {ι : Type*} [Fintype ι] (hS : IsOpen S)
    (u : ι → WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : ∀ i, HasSmoothDirichletH2Approximation (u i)) :
    HasSmoothDirichletH2Approximation (∑ i, u i) := by
  choose F hF hD ht using hu
  let U (n : ℕ) := SpatialTest.sumTest (fun i => F i n)
  have he (n : ℕ) : (U n).allOrderJetOn S 2=∑ i, (F i n).allOrderJetOn S 2 :=
    SpatialTest.sumTest_allOrderJetOn hS _ 2
  refine ⟨U,?_,?_,?_⟩
  · intro n x hx
    change (∑ i, (F i n).value) x=0
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hF i n x hx
  · intro n
    rw [he,map_sum]
    exact (dirichletJetSpace S).sum_mem fun i _ => hD i n
  · have hs := tendsto_finsetSum Finset.univ (fun i _ => ht i)
    have heq : (fun n => (U n).allOrderJetOn S 2)=(fun n => ∑ i, (F i n).allOrderJetOn S 2) := funext he
    rwa [heq]

theorem hasSmoothDirichletH2Approximation_of_finite_cover {ι : Type*} [Fintype ι]
    (hS : IsOpen S) (hregS : DirichletH2Regular S)
    (V : ι → Set (SpatialCoordinates d)) (hV : ∀ i, IsOpen (V i))
    (hb : ∀ i, Bornology.IsBounded (V i)) (hcover : closure S⊆⋃ i, V i)
    (u : dirichletH2JetSpace S)
    (hlocal : ∀ i (η : SpatialTest (univ : Set (SpatialCoordinates d))), tsupport η.value⊆V i →
      HasSmoothDirichletH2Approximation (η.cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u)) :
    HasSmoothDirichletH2Approximation u.val := by
  obtain ⟨η,hsupp,_,hsum⟩ := exists_finite_smooth_partition isClosed_closure V hV hb hcover
  have hh := hasSmoothDirichletH2Approximation_sum hS
    (fun i => (η i).cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u)
    (fun i => hlocal i (η i) (hsupp i))
  rwa [SpatialTest.cutoffH2Transfer_partition hS hregS η (fun x hx => hsum x (subset_closure hx)) u] at hh

theorem hasSmoothDirichletH2Approximation_of_compact_closure_local
    (hS : IsOpen S) (hregS : DirichletH2Regular S) (hcompact : IsCompact (closure S))
    (u : dirichletH2JetSpace S)
    (hlocal : ∀ c∈closure S, ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ c∈V ∧ Bornology.IsBounded V ∧
      ∀ η : SpatialTest (univ : Set (SpatialCoordinates d)), tsupport η.value⊆V →
        HasSmoothDirichletH2Approximation (η.cutoffH2Transfer hS hS inter_subset_left inter_subset_left hregS u)) :
    HasSmoothDirichletH2Approximation u.val := by
  choose V hV hcV hb hh using fun c : closure S => hlocal c.val c.property
  have hcover : closure S⊆⋃ c : closure S, V c := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hcV ⟨x,hx⟩⟩
  obtain ⟨I,hI⟩ := hcompact.elim_finite_subcover V hV hcover
  have hcoverI : closure S⊆⋃ c : I, V c.val := by
    intro x hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp (hI hx)
    obtain ⟨hc,hxc⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨⟨c,hc⟩,hxc⟩
  exact hasSmoothDirichletH2Approximation_of_finite_cover hS hregS
    (fun c : I => V c.val) (fun c => hV c.val) (fun c => hb c.val) hcoverI u (fun c => hh c.val)

theorem regular_analytic_sublevel_strong_h2_approximation (hd : 0<d)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ω g) (a : ℝ) (hb : Bornology.IsBounded {x | g x<a})
    (hreg : ∀ c∈frontier {x | g x<a}, g c=a ∧ fderiv ℝ g c≠0)
    (u : dirichletH2JetSpace {x | g x<a}) : HasSmoothDirichletH2Approximation u.val := by
  have hS : IsOpen {x | g x<a} := isOpen_lt hg.continuous continuous_const
  have hregS : DirichletH2Regular {x | g x<a} := by
    intro v hv f hf
    obtain ⟨U,hU,_⟩ := exists_dirichlet_H2_of_regular_analytic_sublevel g hg a hb hreg v hv f hf
    exact ⟨U,hU⟩
  apply hasSmoothDirichletH2Approximation_of_compact_closure_local hS hregS hb.isCompact_closure u
  intro c hc
  by_cases hcS : c∈{x | g x<a}
  · exact exists_interior_local_strong_h2_approximation hd hS hregS hcS u
  · have hcF : c∈frontier {x | g x<a} := by rw [hS.frontier_eq]; exact ⟨hc,hcS⟩
    exact exists_boundary_local_strong_h2_approximation g hg a hregS c (hreg c hcF).1 (hreg c hcF).2 u

theorem halfspaceSmoothInner_strong_h2_approximation {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {z : SpatialCoordinates d} (hz : z∈halfspaceSmoothInner ℓ b n)
    (u : dirichletH2JetSpace (halfspaceSmoothInner ℓ b n)) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ k, ∀ x∈frontier (halfspaceSmoothInner ℓ b n), (U k).value x=0) ∧
      (∀ k, WeakSobolevJet.truncate (by decide : 1≤2)
        ((U k).allOrderJetOn (halfspaceSmoothInner ℓ b n) 2)∈dirichletJetSpace (halfspaceSmoothInner ℓ b n)) ∧
      Tendsto (fun k => (U k).allOrderJetOn (halfspaceSmoothInner ℓ b n) 2) atTop (𝓝 u.val) :=
  regular_analytic_sublevel_strong_h2_approximation hd (halfspaceExpSum ℓ b n)
    (halfspaceExpSum_analytic ℓ b n) (1/2)
    ((halfspaceSmoothInner_compact ℓ b hb n).isBounded.subset subset_closure)
    (fun _ hc => halfspaceSmoothInner_boundary_regular ℓ b n hz hc) u

end Carleman
