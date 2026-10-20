module

public import Carleman.Control.FiniteHalfspaceP1Refinement

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def FiniteHalfspaceP1NullLimits {κidx : Type*} [Fintype κidx]
    (L : κidx → SpatialCoordinates (d+1) →L[ℝ] ℝ) (offset : κidx → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, offset i<L i x})
    (ω : Set (SpatialCoordinates (d+1))) (shape cmesh Bmesh γ : ℝ) : Prop :=
    let S := {x | ∀ i, offset i<L i x}
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
    ∃ κ d0 : ℝ, 0 < κ ∧ 0 < d0 ∧ ∀ T M : ℝ, 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (mesh : ∀ n, SimplicialPartition S (ι n)),
        (∀ n, (mesh n).FaceMatching) → (∀ n, (mesh n).BoundaryFitted) →
      ∀ (centers : ∀ n, ι n → SpatialCoordinates (d+1)) (r ℓ : ∀ n, ι n → ℝ),
        (∀ n i, 0 < r n i) → (∀ n i, Metric.ball (centers n i) (r n i) ⊆ (mesh n).cell i) →
        (∀ n i, (mesh n).cellDiameter i ≤ shape*r n i) → (∀ n i, 0 < ℓ n i) →
        (∀ n i, cmesh*(mesh n).cellDiameter i ≤ ℓ n i) →
        (∀ n i, ℓ n i ≤ Bmesh*(mesh n).cellDiameter i) →
        (∀ n i j, (mesh n).VertexNeighbors i j → ℓ n j ≤ γ*ℓ n i) →
        Tendsto (fun n => (mesh n).maxDiameter) atTop (𝓝 0) →
      ∀ (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T),
        Tendsto (fun n => (g n).dt) atTop (𝓝 0) →
      ∀ b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)),
        b.bound ≤ M → ∀ y0 : Lp ℝ 2 (volume.restrict S),
      let X := fun n => (mesh n).conformingSpace (dirichletSubspace S);
      let hX := fun n => (mesh n).conformingSpace_le (dirichletSubspace S);
      let bg := fun n => fixedTimeCellPotential T (g n) (hT n) b;
      ∃ J : ℕ,
      ∃ u : ∀ n, Fin (g (n+J)).steps → Lp ℝ 2 ((volume.restrict S).restrict ω),
      ∃ y : ∀ n, Fin ((g (n+J)).steps+1) → X (n+J),
        (∀ n, (g (n+J)).dt*M ≤ 1/2) ∧
        (∀ n, y n 0=(X (n+J)).orthogonalProjectionOnto y0 ∧
          ForwardEquation (g (n+J)).dt
            (fun i => galerkinStiffness (boundedDirichletOriginalForm (finite_halfspace_isOpen L offset) (Nat.zero_lt_succ d) hbounded) (X (n+J)) (hX (n+J))+
              conformingPotential (X (n+J)) (bg (n+J) i))
            (conformingRegionControl (X (n+J)) ω) (u n) (y n) ∧
          controlNorm (g (n+J)).dt (u n) ≤ Real.sqrt C*‖(X (n+J)).orthogonalProjectionOnto y0‖ ∧
          ‖y n (Fin.last (g (n+J)).steps)‖ ≤
            Real.sqrt C*Real.exp (-d0*physicalMeshScale κ (mesh (n+J)).maxDiameter (g (n+J)).dt)*
              ‖(X (n+J)).orthogonalProjectionOnto y0‖ ∧
          ‖fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => (restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i))‖ ≤ Real.sqrt C*‖y0‖ ∧
          (∀ᵐ t ∂volume.restrict (Ioc 0 T), fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => (restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i)) t ∈ supportedRegionSpace ω)) ∧
        Tendsto (fun n => (y n 0 : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 y0) ∧
        Tendsto (fun n => ‖y n (Fin.last (g (n+J)).steps)‖) atTop (𝓝 0) ∧
        Tendsto (fun n => (y n (Fin.last (g (n+J)).steps) : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 0) ∧
        let K := fun n => fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
          (fun i => (restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i));
        (∀ σ : ℕ → ℕ, ∃ v : Lp (Lp ℝ 2 ((volume.restrict S).restrict ω)) 2 (volume.restrict (Ioc 0 T)),
          ‖v‖ ≤ Real.sqrt C*‖y0‖ ∧ ∃ χ : ℕ → ℕ, StrictMono χ ∧
          ∀ w, Tendsto (fun n => inner ℝ (K (σ (χ n))) w) atTop
            (𝓝 (inner ℝ ((restrictRegionCLM (ν := volume.restrict S) (E := ℝ) ω).adjoint.compLp v) w))) ∧
        (∀ σ : ℕ → ℕ, StrictMono σ →
          ∀ U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)),
          (∀ w, Tendsto (fun n => inner ℝ (K (σ n)) w) atTop (𝓝 (inner ℝ U w))) →
          ∃ Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)),
            ‖Y‖ ≤ stateTimeEnergyBound T M ‖y0‖ (Real.sqrt C*‖y0‖) ∧
            ∃ v : Lp (Lp ℝ 2 ((volume.restrict S).restrict ω)) 2 (volume.restrict (Ioc 0 T)),
              (restrictRegionCLM (ν := volume.restrict S) (E := ℝ) ω).adjoint.compLp v=U ∧
              ‖v‖ ≤ Real.sqrt C*‖y0‖ ∧ FiniteDirichletControlIdentity T S b y0 Y U ∧
              DirichletNullControlState T S (finite_halfspace_isOpen L offset) b y0 Y U)

theorem finite_halfspace_p1_controls_null_limits {κidx : Type*} [Fintype κidx] (hdim : d+1 ≤ 3)
    (L : κidx → SpatialCoordinates (d+1) →L[ℝ] ℝ) (offset : κidx → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, offset i<L i x})
    {ω : Set (SpatialCoordinates (d+1))} (hω : IsOpen ω) (hne : ω.Nonempty)
    (hωS : ω ⊆ {x | ∀ i, offset i<L i x})
    (shape cmesh Bmesh γ : ℝ) (hshape : 0 < shape) (hcmesh : 0 < cmesh) (hBmesh : 0 < Bmesh)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit (d+1)) :
    FiniteHalfspaceP1NullLimits L offset hbounded ω shape cmesh Bmesh γ := by
  unfold FiniteHalfspaceP1NullLimits
  intro S
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
  let a := boundedDirichletOriginalForm (finite_halfspace_isOpen L offset) (Nat.zero_lt_succ d)
    hbounded
  obtain ⟨κ,d0,hκ,hd0,hcontrol⟩ := finite_halfspace_p1_controls_independent_refinement hdim L offset hbounded
    hω hne hωS shape cmesh Bmesh γ hshape hcmesh hBmesh hγ hΓ
  refine ⟨κ,d0,hκ,hd0,?_⟩
  intro T M hTpos hM
  obtain ⟨C,hC,hdata⟩ := hcontrol T M hTpos hM
  refine ⟨C,hC,?_⟩
  intro ι _ mesh hmesh hboundary centers r ℓ hr hball hsh hℓ hlow hupp hg hlim g hT htlim b hb y0 X hX bg
  obtain ⟨J,u,y,hsmall,hall,hy0,hyN,hET⟩ :=
    hdata ι mesh hmesh hboundary centers r ℓ hr hball hsh hℓ hlow hupp hg hlim g hT htlim b hb y0
  refine ⟨J,u,y,hsmall,hall,hy0,hyN,hET,?_⟩
  intro K
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hKn n : ‖K n‖ ≤ Real.sqrt C*‖y0‖ := (hall n).2.2.2.2.1
  have hKs n : ∀ᵐ t ∂volume.restrict (Ioc 0 T), K n t ∈ supportedRegionSpace ω := (hall n).2.2.2.2.2
  constructor
  · intro σ
    exact exists_regional_control_weak_subsequence (volume.restrict (Ioc 0 T)) ω hω.measurableSet
      (fun n => K (σ n)) (fun n => hKs (σ n)) (fun n => hKn (σ n))
  · intro σ hσ U hU
    obtain ⟨v,hv,hn,hvbound⟩ := regional_control_of_weak_limit (volume.restrict (Ioc 0 T)) ω hω.measurableSet
      (fun n => K (σ n)) U (fun n => hKs (σ n)) (fun n => hKn (σ n)) hU
    have htail : Tendsto (fun n => σ n+J) atTop atTop := (tendsto_add_atTop_nat J).comp hσ.tendsto_atTop
    obtain ⟨Y,hY,hidentity,hnull⟩ := full_p1_weak_control_limit_null_state
      (finite_halfspace_isOpen L offset) (finite_halfspace_convex L offset) (Nat.zero_lt_succ d)
      hbounded
      (fun n => mesh (σ n+J)) (fun n => hmesh (σ n+J)) (fun n => hboundary (σ n+J)) hshape.le
      (fun n => centers (σ n+J)) (fun n => r (σ n+J)) (fun n => hr (σ n+J))
      (fun n => hball (σ n+J)) (fun n => hsh (σ n+J)) (hlim.comp htail)
      T M (Real.sqrt C*‖y0‖) hM (by positivity) (fun n => g (σ n+J)) (fun n => hT (σ n+J))
      (htlim.comp htail) (fun n => hsmall (σ n)) ω hω.measurableSet b hb
      (fun n => u (σ n)) (fun n => y (σ n)) (fun n => (hall (σ n)).2.1)
      y0 (fun n => (hall (σ n)).1)
      (fun n => by simpa only [K,regional_time_control_norm T _ _ ω hω.measurableSet] using hKn (σ n))
      (hyN.comp hσ.tendsto_atTop) U hU
    exact ⟨Y,hY,v,hv,hvbound,hidentity,hnull⟩

end Carleman.Physical
