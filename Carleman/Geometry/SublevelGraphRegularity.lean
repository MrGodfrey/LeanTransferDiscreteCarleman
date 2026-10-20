module
public import Carleman.Geometry.SmoothGraphHeightExtension
public import Carleman.Spatial.BoundaryCutoffTransfer
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-! The actual sign of the original normal derivative identifies the sublevel
side. Genuine cutoffs then yield local boundary H² for the original weak state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def coordinateLine (r : Fin d) (x : SpatialCoordinates d) (t : ℝ) : SpatialCoordinates d :=
  x+(t-x r) • EuclideanSpace.basisFun (Fin d) ℝ r

theorem coordinateLine_self (r : Fin d) (x : SpatialCoordinates d) : coordinateLine r x (x r)=x := by
  simp [coordinateLine]

theorem coordinateLine_hasDerivAt (r : Fin d) (x : SpatialCoordinates d) (t : ℝ) :
    HasDerivAt (coordinateLine r x) (EuclideanSpace.basisFun (Fin d) ℝ r) t := by
  unfold coordinateLine
  simpa only [id_eq,one_smul] using
    (((hasDerivAt_id t).sub_const (x r)).smul_const (EuclideanSpace.basisFun (Fin d) ℝ r)).const_add x

theorem coordinateLine_convex_preimage (r : Fin d) (x : SpatialCoordinates d)
    {U : Set (SpatialCoordinates d)} (hU : Convex ℝ U) : Convex ℝ ((coordinateLine r x) ⁻¹' U) := by
  intro a ha b hb α β hα hβ hsum
  change coordinateLine r x (α*a+β*b) ∈ U
  have he : α • coordinateLine r x a+β • coordinateLine r x b=coordinateLine r x (α*a+β*b) := by
    dsimp only [coordinateLine]
    rw [smul_add,smul_add,smul_smul,smul_smul]
    calc
      _ = (α+β) • x+(α*(a-x r)+β*(b-x r)) • EuclideanSpace.basisFun (Fin d) ℝ r := by
        rw [add_smul,add_smul]
        abel
      _ = _ := by
        rw [hsum,one_smul]
        congr 2
        nlinarith [congrArg (fun z : ℝ => z*x r) hsum]
  rw [← he]
  exact hU ha hb hα hβ hsum

theorem coordinateLine_lt_iff_of_positive (r : Fin d) (x : SpatialCoordinates d)
    (g : SpatialCoordinates d → ℝ) (hg : Differentiable ℝ g)
    {U : Set (SpatialCoordinates d)} (hU : Convex ℝ U)
    (hpos : ∀ y ∈ U, 0 < fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ r))
    {a b : ℝ} (ha : coordinateLine r x a ∈ U) (hb : coordinateLine r x b ∈ U) :
    g (coordinateLine r x a)<g (coordinateLine r x b) ↔ a<b := by
  let f := g ∘ coordinateLine r x
  have hd (t : ℝ) : HasDerivAt f (fderiv ℝ g (coordinateLine r x t) (EuclideanSpace.basisFun (Fin d) ℝ r)) t :=
    (hg _).hasFDerivAt.comp_hasDerivAt t (coordinateLine_hasDerivAt r x t)
  have hf : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hmono : StrictMonoOn f ((coordinateLine r x) ⁻¹' U) := by
    apply strictMonoOn_of_deriv_pos (coordinateLine_convex_preimage r x hU)
    · exact hf.continuous.continuousOn
    · intro t ht
      rw [(hd t).deriv]
      have ht' : t ∈ (coordinateLine r x) ⁻¹' U := interior_subset ht
      exact hpos _ ht'
  exact hmono.lt_iff_lt ha hb

theorem coordinateLine_lt_iff_of_negative (r : Fin d) (x : SpatialCoordinates d)
    (g : SpatialCoordinates d → ℝ) (hg : Differentiable ℝ g)
    {U : Set (SpatialCoordinates d)} (hU : Convex ℝ U)
    (hneg : ∀ y ∈ U, fderiv ℝ g y (EuclideanSpace.basisFun (Fin d) ℝ r) < 0)
    {a b : ℝ} (ha : coordinateLine r x a ∈ U) (hb : coordinateLine r x b ∈ U) :
    g (coordinateLine r x a)<g (coordinateLine r x b) ↔ b<a := by
  have hp (y) (hy : y ∈ U) : 0 < fderiv ℝ (fun z => -g z) y (EuclideanSpace.basisFun (Fin d) ℝ r) := by
    change 0 < fderiv ℝ (-g) y (EuclideanSpace.basisFun (Fin d) ℝ r)
    rw [(hg y).hasFDerivAt.neg.fderiv]
    simpa only [neg_apply,neg_pos] using hneg y hy
  simpa only [neg_lt_neg_iff] using coordinateLine_lt_iff_of_positive r x (fun z => -g z) hg.neg hU hp hb ha

theorem exists_sublevel_hypograph_near_of_positive (r : Fin d) (g Ψ : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hΨ : Continuous Ψ) (c : SpatialCoordinates d)
    (hcΨ : Ψ c=c r) (hpos : 0 < fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r))
    {N : Set (SpatialCoordinates d)} (hN : IsOpen N) (hcN : c ∈ N)
    (hgraph : ∀ x ∈ N, g (coordinateLevelMap r Ψ x)=g c) :
    ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ c ∈ V ∧ V ⊆ N ∧
      ∀ x ∈ V, g x<g c ↔ x r<Ψ x := by
  have hD : Continuous (fun x => fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ r)) :=
    (contDiff_infty_iff_fderiv.mp hg).2.continuous.clm_apply continuous_const
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hD).mem_nhds hpos)
  let G := coordinateLevelMap r Ψ
  have hG : Continuous G := continuous_id.add ((hΨ.sub (EuclideanSpace.proj r).continuous).smul continuous_const)
  have hGc : G c=c := by simp [G,coordinateLevelMap,hcΨ]
  let V := N ∩ ball c ε ∩ G ⁻¹' ball c ε
  have hcV : c ∈ V := ⟨⟨hcN,mem_ball_self hε⟩,by simpa only [mem_preimage,hGc] using mem_ball_self hε⟩
  refine ⟨V,(hN.inter isOpen_ball).inter (isOpen_ball.preimage hG),hcV,fun _ hx => hx.1.1,?_⟩
  intro x hx
  have hh := coordinateLine_lt_iff_of_positive r x g (hg.differentiable (by simp))
    (convex_ball c ε) (fun y hy => hball hy)
    (a := x r) (b := Ψ x) (by simpa only [coordinateLine_self] using hx.1.2) hx.2
  have he : coordinateLine r x (Ψ x)=coordinateLevelMap r Ψ x := rfl
  rw [coordinateLine_self,he,hgraph x hx.1.1] at hh
  exact hh

theorem exists_sublevel_epigraph_near_of_negative (r : Fin d) (g Ψ : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hΨ : Continuous Ψ) (c : SpatialCoordinates d)
    (hcΨ : Ψ c=c r) (hneg : fderiv ℝ g c (EuclideanSpace.basisFun (Fin d) ℝ r)<0)
    {N : Set (SpatialCoordinates d)} (hN : IsOpen N) (hcN : c ∈ N)
    (hgraph : ∀ x ∈ N, g (coordinateLevelMap r Ψ x)=g c) :
    ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ c ∈ V ∧ V ⊆ N ∧
      ∀ x ∈ V, g x<g c ↔ Ψ x<x r := by
  have hD : Continuous (fun x => fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ r)) :=
    (contDiff_infty_iff_fderiv.mp hg).2.continuous.clm_apply continuous_const
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt hD continuous_const).mem_nhds hneg)
  let G := coordinateLevelMap r Ψ
  have hG : Continuous G := continuous_id.add ((hΨ.sub (EuclideanSpace.proj r).continuous).smul continuous_const)
  have hGc : G c=c := by simp [G,coordinateLevelMap,hcΨ]
  let V := N ∩ ball c ε ∩ G ⁻¹' ball c ε
  have hcV : c ∈ V := ⟨⟨hcN,mem_ball_self hε⟩,by simpa only [mem_preimage,hGc] using mem_ball_self hε⟩
  refine ⟨V,(hN.inter isOpen_ball).inter (isOpen_ball.preimage hG),hcV,fun _ hx => hx.1.1,?_⟩
  intro x hx
  have hh := coordinateLine_lt_iff_of_negative r x g (hg.differentiable (by simp))
    (convex_ball c ε) (fun y hy => hball hy)
    (a := x r) (b := Ψ x) (by simpa only [coordinateLine_self] using hx.1.2) hx.2
  have he : coordinateLine r x (Ψ x)=coordinateLevelMap r Ψ x := rfl
  rw [coordinateLine_self,he,hgraph x hx.1.1] at hh
  exact hh

theorem exists_sublevel_graph_near_regular (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (a : ℝ) (c : SpatialCoordinates d)
    (hc : g c=a) (hreg : fderiv ℝ g c ≠ 0) :
    ∃ (r : Fin d) (Ψ : SpatialCoordinates d → ℝ) (C : NNReal) (B : Fin d → NNReal)
      (V : Set (SpatialCoordinates d)),
      IsOpen V ∧ c ∈ V ∧ ContDiff ℝ ∞ Ψ ∧ LipschitzWith C Ψ ∧
      (∀ i : Fin d, LipschitzWith (B i) (fun x => fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))) ∧
      (∀ (x : SpatialCoordinates d) (t : ℝ), Ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=Ψ x) ∧
      ((∀ x ∈ V, g x<a ↔ Ψ x<x r) ∨ (∀ x ∈ V, g x<a ↔ x r<Ψ x)) := by
  obtain ⟨r,Ψ,C,B,N,hN,hcN,hΨ,hC,hB,hinv,hcΨ,hr,hgraph,_⟩ :=
    exists_bounded_smooth_coordinate_level_height g hg c hreg
  rcases lt_or_gt_of_ne hr with hn | hp
  · obtain ⟨V,hV,hcV,_,hside⟩ := exists_sublevel_epigraph_near_of_negative r g Ψ
      (hg.of_le le_top) hΨ.continuous c hcΨ hn hN hcN hgraph
    refine ⟨r,Ψ,C,B,V,hV,hcV,hΨ,hC,hB,hinv,Or.inl ?_⟩
    simpa only [hc] using hside
  · obtain ⟨V,hV,hcV,_,hside⟩ := exists_sublevel_hypograph_near_of_positive r g Ψ
      (hg.of_le le_top) hΨ.continuous c hcΨ hp hN hcN hgraph
    refine ⟨r,Ψ,C,B,V,hV,hcV,hΨ,hC,hB,hinv,Or.inr ?_⟩
    simpa only [hc] using hside

theorem exists_spatial_cutoff_one_near {V : Set (SpatialCoordinates d)} (hV : IsOpen V)
    {c : SpatialCoordinates d} (hc : c ∈ V) :
    ∃ (δ : ℝ) (η : SpatialTest (univ : Set (SpatialCoordinates d))),
      0 < δ ∧ ball c δ ⊆ V ∧ tsupport η.value ⊆ V ∧ ∀ x ∈ ball c δ, η.value x=1 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hc)
  let β : ContDiffBump c := ⟨ε/4,ε/2,by positivity,by linarith⟩
  let η : SpatialTest (univ : Set (SpatialCoordinates d)) :=
    ⟨β,β.contDiff,β.hasCompactSupport,subset_univ _⟩
  refine ⟨ε/4,η,by positivity,(ball_subset_ball (by linarith)).trans hball,?_,?_⟩
  · change tsupport β ⊆ V
    rw [β.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [β]; linarith)).trans hball
  · intro x hx
    exact β.one_of_mem_closedBall (ball_subset_closedBall hx)

open MeasureTheory

theorem exists_local_dirichlet_H2_of_regular_level (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ω g) (a : ℝ) (c : SpatialCoordinates d)
    (hc : g c=a) (hreg : fderiv ℝ g c ≠ 0)
    (u : WeakSobolevJet d 1 (volume.restrict {x | g x<a}) {x | g x<a})
    (hu : u ∈ dirichletJetSpace {x | g x<a})
    (f : Lp ℝ 2 (volume.restrict {x | g x<a})) (hf : IsWeakNegativeLaplacian u f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : WeakSobolevJet d 2
      (volume.restrict ({x | g x<a} ∩ ball c δ)) ({x | g x<a} ∩ ball c δ),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=
        WeakSobolevJet.restrictSubdomain inter_subset_left u := by
  obtain ⟨r,Ψ,C,B,V,hV,hcV,hΨ,hC,hB,hinv,hside⟩ := exists_sublevel_graph_near_regular g hg a c hc hreg
  obtain ⟨δ,η,hδ,hball,hsupp,hη⟩ := exists_spatial_cutoff_one_near hV hcV
  have hS : IsOpen {x | g x<a} := isOpen_lt hg.continuous continuous_const
  have hR : IsOpen ({x | g x<a} ∩ ball c δ) := hS.inter isOpen_ball
  refine ⟨δ,hδ,?_⟩
  rcases hside with hside | hside
  · exact η.exists_local_H2_of_cutoff_graph_epigraph hS hR r Ψ hΨ hC hinv hB
      (fun x hx => (hside x (hsupp hx.2)).mp hx.1)
      (fun x hx => (hside x (hsupp hx.2)).mpr hx.1)
      inter_subset_left (fun x hx => (hside x (hball hx.2)).mp hx.1)
      (fun x hx => hη x hx.2) u hu f hf
  · exact η.exists_local_H2_of_cutoff_graph_hypograph hS hR r Ψ hΨ hC hinv hB
      (fun x hx => (hside x (hsupp hx.2)).mp hx.1)
      (fun x hx => (hside x (hsupp hx.2)).mpr hx.1)
      inter_subset_left (fun x hx => (hside x (hball hx.2)).mp hx.1)
      (fun x hx => hη x hx.2) u hu f hf

theorem halfspaceSmoothInner_local_boundary_H2 {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    {c : SpatialCoordinates d} (hc : c ∈ frontier (halfspaceSmoothInner ℓ b n))
    (u : WeakSobolevJet d 1 (volume.restrict (halfspaceSmoothInner ℓ b n)) (halfspaceSmoothInner ℓ b n))
    (hu : u ∈ dirichletJetSpace (halfspaceSmoothInner ℓ b n))
    (f : Lp ℝ 2 (volume.restrict (halfspaceSmoothInner ℓ b n))) (hf : IsWeakNegativeLaplacian u f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : WeakSobolevJet d 2
      (volume.restrict (halfspaceSmoothInner ℓ b n ∩ ball c δ)) (halfspaceSmoothInner ℓ b n ∩ ball c δ),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=
        WeakSobolevJet.restrictSubdomain inter_subset_left u := by
  obtain ⟨he,hr⟩ := halfspaceSmoothInner_boundary_regular ℓ b n hz hc
  exact exists_local_dirichlet_H2_of_regular_level (halfspaceExpSum ℓ b n)
    (halfspaceExpSum_analytic ℓ b n) (1/2) c he hr u hu f hf

end Carleman
