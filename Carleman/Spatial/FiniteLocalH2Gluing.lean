module
public import Carleman.Geometry.SublevelGraphRegularity
public import Carleman.Spatial.InteriorPoissonRegularity
public import Mathlib.Geometry.Manifold.PartitionOfUnity
/-! A genuine finite smooth partition transfers every local Hessian test
identity and yields global H² of the same original weak Dirichlet state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators ContDiff Manifold
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem exists_finite_smooth_partition {ι : Type*} [Fintype ι]
    {K : Set (SpatialCoordinates d)} (hK : IsClosed K)
    (V : ι → Set (SpatialCoordinates d)) (hV : ∀ i, IsOpen (V i))
    (hb : ∀ i, Bornology.IsBounded (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ η : ι → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ i, tsupport (η i).value ⊆ V i) ∧
      (∀ i x, 0 ≤ (η i).value x ∧ (η i).value x ≤ 1) ∧
      ∀ x ∈ K, ∑ i, (η i).value x=1 := by
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, SpatialCoordinates d)) hK V hV hcover
  let η : ι → SpatialTest (univ : Set (SpatialCoordinates d)) := fun i =>
    ⟨ρ i,(ρ i).contMDiff.contDiff,
      (hb i).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) ((hρ i).trans subset_closure),subset_univ _⟩
  refine ⟨η,hρ,(fun i x => ⟨ρ.nonneg i x,ρ.le_one i x⟩),?_⟩
  intro x hx
  change (∑ i, ρ i x)=1
  exact ρ.sum_finsupport' x hx (Finset.subset_univ _)

theorem SpatialTest.monoDomain_inner (hS : IsOpen S) (hT : IsOpen T) (hTS : T ⊆ S)
    (φ : SpatialTest T) (v : Lp ℝ 2 (volume.restrict S)) :
    inner ℝ v ((φ.monoDomain hTS).toLp (volume.restrict S))=
      inner ℝ (subdomainLp hTS v) (φ.toLp (volume.restrict T)) := by
  have he := congrArg WeakSobolevJet.value (WeakSobolevJet.extendDirichlet_test hS hT hTS φ)
  rw [WeakSobolevJet.extendDirichlet_value,SpatialTest.sobolevJet_value,SpatialTest.sobolevJet_value] at he
  change subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T))=
    (φ.monoDomain hTS).toLp (volume.restrict S) at he
  rw [← he]
  calc
    _ = inner ℝ (subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T))) v := real_inner_comm _ _
    _ = inner ℝ (φ.toLp (volume.restrict T)) (subdomainLp hTS v) := subdomainZeroExtend_inner hT.measurableSet hTS _ _
    _ = _ := real_inner_comm _ _

theorem SpatialTest.monoDomain_derivative_inner (hS : IsOpen S) (hT : IsOpen T) (hTS : T ⊆ S)
    (φ : SpatialTest T) (v : Lp ℝ 2 (volume.restrict S)) (e : SpatialCoordinates d) :
    inner ℝ v ((φ.monoDomain hTS).derivativeLp (volume.restrict S) e)=
      inner ℝ (subdomainLp hTS v) (φ.derivativeLp (volume.restrict T) e) := by
  have hh := (φ.derivativeTest e).monoDomain_inner hS hT hTS v
  rw [SpatialTest.derivativeTest_toLp] at hh
  change inner ℝ v (((φ.monoDomain hTS).derivativeTest e).toLp (volume.restrict S))=_ at hh
  rwa [SpatialTest.derivativeTest_toLp] at hh

theorem SpatialTest.cutoffTransfer_toLp_norm_le (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hη : ∀ x, |η.value x| ≤ 1) (φ : SpatialTest S)
    (hST : S ∩ tsupport η.value ⊆ T) (hTS : T ⊆ S) :
    ‖(η.cutoffTransfer φ hST).toLp (volume.restrict T)‖ ≤ ‖φ.toLp (volume.restrict S)‖ := by
  apply le_trans (b := ‖subdomainLp hTS (φ.toLp (volume.restrict S))‖) _ (subdomainLp_norm_le hTS _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(η.cutoffTransfer φ hST).toLp_ae (volume.restrict T),
    subdomainLp_ae hTS (φ.toLp (volume.restrict S)),
    (φ.toLp_ae (volume.restrict S)).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl))] with x hc hs ht
  rw [hc,hs,ht]
  change ‖η.value x*φ.value x‖ ≤ ‖φ.value x‖
  rw [norm_mul,Real.norm_eq_abs (η.value x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hη x)

theorem SpatialTest.partition_jet {ι : Type*} [Fintype ι]
    (hS : IsOpen S) (η : ι → SpatialTest (univ : Set (SpatialCoordinates d)))
    (hsum : ∀ x ∈ S, ∑ i, (η i).value x=1)
    (R : ι → Set (SpatialCoordinates d)) (hRS : ∀ i, R i ⊆ S)
    (hsupp : ∀ i, S ∩ tsupport (η i).value ⊆ R i) (φ : SpatialTest S) :
    φ.sobolevJet=∑ i, (((η i).cutoffTransfer φ (hsupp i)).monoDomain (hRS i)).sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  simp only [map_sum,SpatialTest.sobolevJet_value]
  apply Lp.ext
  have hae := eventuallyEq_sum (s := Finset.univ) (fun i _ =>
    (((η i).cutoffTransfer φ (hsupp i)).monoDomain (hRS i)).toLp_ae (volume.restrict S))
  filter_upwards [φ.toLp_ae (volume.restrict S),
    Lp.coeFn_finsetSum Finset.univ (fun i => (((η i).cutoffTransfer φ (hsupp i)).monoDomain (hRS i)).toLp (volume.restrict S)),
    hae,ae_restrict_mem hS.measurableSet] with x hx hsumLp hvals hxs
  rw [hx,hsumLp,hvals]
  simp only [Finset.sum_apply]
  change φ.value x=∑ i, (η i).value x*φ.value x
  rw [← Finset.sum_mul,hsum x hxs,one_mul]

theorem exists_H2_of_finite_local_partition {ι : Type*} [Fintype ι]
    (hS : IsOpen S) (η : ι → SpatialTest (univ : Set (SpatialCoordinates d)))
    (hη : ∀ i x, |(η i).value x| ≤ 1) (hsum : ∀ x ∈ S, ∑ i, (η i).value x=1)
    (R : ι → Set (SpatialCoordinates d)) (hR : ∀ i, IsOpen (R i)) (hRS : ∀ i, R i ⊆ S)
    (hsupp : ∀ i, S ∩ tsupport (η i).value ⊆ R i)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (U : ∀ i, WeakSobolevJet d 2 (volume.restrict (R i)) (R i))
    (hU : ∀ i, WeakSobolevJet.truncate (by omega : 1 ≤ 2) (U i)=WeakSobolevJet.restrictSubdomain (hRS i) u) :
    ∃ W : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) W=u ∧
      ‖WeakSobolevJet.field 2 W‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*(∑ i, ‖WeakSobolevJet.field 2 (U i)‖)^2 := by
  apply exists_weakH2_of_gradient_test_bounds hS u (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro i j φ
  let χ := fun k => (η k).cutoffTransfer φ (hsupp k)
  have hD := congrArg (fun w => derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 w))
    (φ.partition_jet hS η hsum R hRS hsupp)
  simp only [map_sum,SpatialTest.sobolevJet_derivative] at hD
  rw [hD,inner_sum]
  calc
    _ ≤ ∑ k, |inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (((χ k).monoDomain (hRS k)).derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖WeakSobolevJet.field 2 (U k)‖*‖φ.toLp (volume.restrict S)‖ := by
      apply Finset.sum_le_sum
      intro k _
      have hgrad := congrArg (WeakSobolevJet.field 1) (hU k)
      change WeakSobolevJet.field 1 (U k)=subdomainLp (hRS k) (WeakSobolevJet.field 1 u) at hgrad
      have hw := (U k).property 1 (Sym.cons i Sym.nil) j (χ k)
      change inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (U k)))
        ((χ k).derivativeLp (volume.restrict (R k)) (EuclideanSpace.basisFun (Fin d) ℝ j))=
          -inner ℝ (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 (U k)))
            ((χ k).toLp (volume.restrict (R k))) at hw
      rw [hgrad,derivativeComponent_subdomain] at hw
      rw [SpatialTest.monoDomain_derivative_inner hS (hR k) (hRS k),hw,abs_neg]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (derivativeComponent_norm_le _ _)
          ((η k).cutoffTransfer_toLp_norm_le (hη k) φ (hsupp k) (hRS k)) (norm_nonneg _) (norm_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem exists_H2_of_finite_local_cover {ι : Type*} [Fintype ι]
    (hS : IsOpen S) (V : ι → Set (SpatialCoordinates d)) (hV : ∀ i, IsOpen (V i))
    (hb : ∀ i, Bornology.IsBounded (V i)) (hcover : closure S ⊆ ⋃ i, V i)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (U : ∀ i, WeakSobolevJet d 2 (volume.restrict (S ∩ V i)) (S ∩ V i))
    (hU : ∀ i, WeakSobolevJet.truncate (by omega : 1 ≤ 2) (U i)=WeakSobolevJet.restrictSubdomain inter_subset_left u) :
    ∃ W : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) W=u := by
  obtain ⟨η,hsupp,hη,hsum⟩ := exists_finite_smooth_partition isClosed_closure V hV hb hcover
  have hη' (i) (x) : |(η i).value x| ≤ 1 := by rw [abs_of_nonneg (hη i x).1]; exact (hη i x).2
  obtain ⟨W,hW,_⟩ := exists_H2_of_finite_local_partition hS η hη' (fun x hx => hsum x (subset_closure hx))
    (fun i => S ∩ V i) (fun i => hS.inter (hV i)) (fun _ => inter_subset_left)
    (fun i _ hx => ⟨hx.1,hsupp i hx.2⟩) u U hU
  exact ⟨W,hW⟩

theorem exists_H2_of_compact_closure_local (hS : IsOpen S) (hcompact : IsCompact (closure S))
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hlocal : ∀ c ∈ closure S, ∃ δ : ℝ, 0 < δ ∧ ∃ U : WeakSobolevJet d 2
      (volume.restrict (S ∩ ball c δ)) (S ∩ ball c δ),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain inter_subset_left u) :
    ∃ W : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) W=u := by
  choose δ hδ U hU using fun c : closure S => hlocal c c.property
  let V := fun c : closure S => ball c.val (δ c)
  have hcover : closure S ⊆ ⋃ c : closure S, V c := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hδ ⟨x,hx⟩)⟩
  obtain ⟨I,hI⟩ := hcompact.elim_finite_subcover V (fun _ => isOpen_ball) hcover
  have hcoverI : closure S ⊆ ⋃ c : I, V c.val := by
    intro x hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp (hI hx)
    obtain ⟨hc,hxc⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨⟨c,hc⟩,hxc⟩
  exact exists_H2_of_finite_local_cover hS (fun c : I => V c.val) (fun _ => isOpen_ball)
    (fun _ => isBounded_ball) hcoverI u (fun c => U c.val) (fun c => hU c.val)

theorem exists_local_interior_H2_ball (hS : IsOpen S) {c : SpatialCoordinates d} (hc : c ∈ S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : WeakSobolevJet d 2
      (volume.restrict (S ∩ ball c δ)) (S ∩ ball c δ),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain inter_subset_left u := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hc)
  have hclosed : closure (S ∩ ball c (ε/2)) ⊆ S := by
    apply subset_trans (closure_mono inter_subset_right)
    rw [closure_ball c (by positivity : ε/2 ≠ 0)]
    exact (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨M,hM,hreg⟩ := exists_interior_H2_bound hS (hS.inter isOpen_ball)
    (isBounded_ball.subset inter_subset_right).isCompact_closure hclosed
  obtain ⟨U,hU,_,_⟩ := hreg u f hf
  exact ⟨ε/2,by positivity,U,hU⟩

theorem exists_dirichlet_H2_of_regular_analytic_sublevel (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (a : ℝ) (hb : Bornology.IsBounded {x | g x<a})
    (hreg : ∀ c ∈ frontier {x | g x<a}, g c=a ∧ fderiv ℝ g c ≠ 0)
    (u : WeakSobolevJet d 1 (volume.restrict {x | g x<a}) {x | g x<a})
    (hu : u ∈ dirichletJetSpace {x | g x<a})
    (f : Lp ℝ 2 (volume.restrict {x | g x<a})) (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict {x | g x<a}) {x | g x<a},
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧ negativeLaplacian U=f := by
  have hS : IsOpen {x | g x<a} := isOpen_lt hg.continuous continuous_const
  have hlocal (c : SpatialCoordinates d) (hc : c ∈ closure {x | g x<a}) :
      ∃ δ : ℝ, 0 < δ ∧ ∃ U : WeakSobolevJet d 2
        (volume.restrict ({x | g x<a} ∩ ball c δ)) ({x | g x<a} ∩ ball c δ),
        WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=WeakSobolevJet.restrictSubdomain inter_subset_left u := by
    by_cases hcS : c ∈ {x | g x<a}
    · exact exists_local_interior_H2_ball hS hcS u f hf
    · have hcF : c ∈ frontier {x | g x<a} := by rw [hS.frontier_eq]; exact ⟨hc,hcS⟩
      exact exists_local_dirichlet_H2_of_regular_level g hg a c (hreg c hcF).1 (hreg c hcF).2 u hu f hf
  obtain ⟨U,hU⟩ := exists_H2_of_compact_closure_local hS hb.isCompact_closure u hlocal
  refine ⟨U,hU,?_⟩
  have hw := negativeLaplacian_isWeak U
  rw [hU] at hw
  exact hw.unique_rhs hS hf

theorem halfspaceSmoothInner_dirichlet_H2 {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hb : Bornology.IsBounded {x | ∀ i, b i < ℓ i x})
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    (u : WeakSobolevJet d 1 (volume.restrict (halfspaceSmoothInner ℓ b n)) (halfspaceSmoothInner ℓ b n))
    (hu : u ∈ dirichletJetSpace (halfspaceSmoothInner ℓ b n))
    (f : Lp ℝ 2 (volume.restrict (halfspaceSmoothInner ℓ b n))) (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict (halfspaceSmoothInner ℓ b n)) (halfspaceSmoothInner ℓ b n),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧ negativeLaplacian U=f := by
  exact exists_dirichlet_H2_of_regular_analytic_sublevel (halfspaceExpSum ℓ b n)
    (halfspaceExpSum_analytic ℓ b n) (1/2)
    ((halfspaceSmoothInner_compact ℓ b hb n).isBounded.subset subset_closure)
    (fun _ hc => halfspaceSmoothInner_boundary_regular ℓ b n hz hc) u hu f hf

end Carleman
