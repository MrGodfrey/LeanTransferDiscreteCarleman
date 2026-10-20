module

public import Carleman.Control.TimeReconstructionEstimates
public import Carleman.Spatial.DirichletForm
public import Carleman.Spatial.HilbertWeakSubsequence
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual H¹₀-valued Bochner reconstructions and weak compactness, with both spatial fields retained. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman

theorem timeCellReconstruction_map
    {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : TimeGrid) (L : H →L[ℝ] G) (u : Fin g.steps → H) :
    L.compLpL 2 (volume.restrict (Ioc 0 g.period)) (timeCellReconstruction g u)=
      timeCellReconstruction g (fun i => L (u i)) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (timeCellReconstruction g u),
    timeCellReconstruction_ae g u, timeCellReconstruction_ae g (fun i => L (u i))] with t ht hu hv
  rw [ht,hu,hv,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t ∈ g.physicalTimeCell i <;> simp [hi]

theorem fixedTimeCellReconstruction_map
    {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T) (L : H →L[ℝ] G) (u : Fin g.steps → H) :
    L.compLpL 2 (volume.restrict (Ioc 0 T)) (fixedTimeCellReconstruction T g hT u)=
      fixedTimeCellReconstruction T g hT (fun i => L (u i)) := by
  subst T
  exact timeCellReconstruction_map g L u

variable {d : ℕ} {S : Set (SpatialCoordinates d)}
/-- The carrier type of the original H¹₀ submodule, with exactly its inherited norm. -/
def DirichletEnergyState (S : Set (SpatialCoordinates d)) : Type := DirichletEnergy S

instance dirichletEnergyStateNormedAddCommGroup : NormedAddCommGroup (DirichletEnergyState S) :=
  (DirichletEnergy S).normedAddCommGroup

instance dirichletEnergyStateInnerProductSpace : InnerProductSpace ℝ (DirichletEnergyState S) :=
  (DirichletEnergy S).innerProductSpace

def dirichletEnergyStateEquiv (S : Set (SpatialCoordinates d)) :
    DirichletEnergyState S ≃ₗᵢ[ℝ] DirichletEnergy S := LinearIsometryEquiv.refl ℝ _

def dirichletStateValue (S : Set (SpatialCoordinates d)) :
    DirichletEnergyState S →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
  conformingEmbed (m := 1) (S := S) (dirichletSubspace S)

def dirichletStateGradient (S : Set (SpatialCoordinates d)) :
    DirichletEnergyState S →L[ℝ] Lp (DerivativeFiber d 1) 2 (volume.restrict S) :=
  dirichletGradient S

theorem dirichletEnergyState_norm_sq (u : DirichletEnergyState S) :
    ‖u‖^2=‖dirichletStateValue S u‖^2+‖dirichletStateGradient S u‖^2 :=
  dirichletEnergy_norm_sq u

theorem dirichletEnergyState_complete (hS : IsOpen S) : CompleteSpace (DirichletEnergyState S) :=
  conformingHilbert_completeSpace _ (dirichletSubspace_closed S hS)

instance dirichletEnergyStateSecondCountable : SecondCountableTopology (DirichletEnergyState S) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (HilbertJetFields d 1 (volume.restrict S)) := inferInstance
  exact inferInstanceAs (SecondCountableTopology (DirichletEnergy S))

theorem dirichlet_time_norm_sq (hS : IsOpen S) (g : TimeGrid) (u : Fin g.steps → DirichletEnergyState S) :
    ‖timeCellReconstruction g u‖^2 =
      ‖timeCellReconstruction g (fun i => dirichletStateValue S (u i))‖^2+
      ‖timeCellReconstruction g (fun i => dirichletStateGradient S (u i))‖^2 := by
  let : CompleteSpace (DirichletEnergyState S) :=
    dirichletEnergyState_complete hS
  have he := timeCellReconstruction_inner g u u
  have hv := timeCellReconstruction_inner g (fun i => dirichletStateValue S (u i))
    (fun i => dirichletStateValue S (u i))
  have hg := timeCellReconstruction_inner g (fun i => dirichletStateGradient S (u i))
    (fun i => dirichletStateGradient S (u i))
  simp only [real_inner_self_eq_norm_sq] at he hv hg
  calc
    _ = g.dt*∑ i, ‖u i‖^2 := he
    _ = g.dt*(∑ i, ‖dirichletStateValue S (u i)‖^2)+
        g.dt*(∑ i, ‖dirichletStateGradient S (u i)‖^2) := by
      have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
        (fun i _ => dirichletEnergyState_norm_sq (u i))
      have hs' := hs.trans (Finset.sum_add_distrib :
        (∑ i, (‖dirichletStateValue S (u i)‖^2+‖dirichletStateGradient S (u i)‖^2))=
          (∑ i, ‖dirichletStateValue S (u i)‖^2)+(∑ i, ‖dirichletStateGradient S (u i)‖^2))
      exact (congrArg (fun a : ℝ => g.dt*a) hs').trans (mul_add _ _ _)
    _ = _ := congrArg₂ (fun a b : ℝ => a+b) hv.symm hg.symm

theorem exists_dirichlet_time_weak_subsequence (hS : IsOpen S) (T : ℝ)
    (u : ℕ → Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)), ‖v‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w, Tendsto (fun n => inner ℝ (u (φ n)) w) atTop (𝓝 (inner ℝ v w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ ((dirichletStateValue S).compLpL 2
          (volume.restrict (Ioc 0 T)) (u (φ n))) w) atTop
        (𝓝 (inner ℝ ((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) v) w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ ((dirichletStateGradient S).compLpL 2
          (volume.restrict (Ioc 0 T)) (u (φ n))) w) atTop
        (𝓝 (inner ℝ ((dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) v) w))) := by
  let : CompleteSpace (DirichletEnergyState S) :=
    dirichletEnergyState_complete hS
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨v,hv,φ,hφ,ht⟩ := exists_hilbert_weak_subsequence u hb
  exact ⟨v,hv,φ,hφ,ht,hilbert_weak_tendsto_map ht ((dirichletStateValue S).compLpL 2 _),
    hilbert_weak_tendsto_map ht ((dirichletStateGradient S).compLpL 2 _)⟩

end Carleman
