module

public import Carleman.Control.BoxCartesianLoadCarleman
public import Carleman.Control.PhysicalObservationUniformProfiles
public import Carleman.Control.ConformingHeatControl

/-! Original relaxed observability for all Cartesian box states and arbitrary bounded nodal potentials. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_cartesian_physical_observability (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W ω : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) (hω : IsOpen ω) (hinc : closure W ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ qc κ h0 Δ0 Cb d0 : ℝ, 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cb ∧ 0 < d0 ∧
      ∀ (T M : ℝ), 0 < T → 0 ≤ M → ∃ C : ℝ, 0 < C ∧
      ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ),
        openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=openCoordinateBox lo hi →
      ∀ h : ℝ, 0 < h → h ≤ h0 → (∀ j, h/ratio ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ g : TimeGrid, g.period = T → g.dt ≤ Δ0 →
        let Smax := physicalMeshScale κ h g.dt
        16*physicalBaseAmplitude Cb qc T M ≤ Smax →
        Smax ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
      ∀ b : Fin g.steps → CartesianInteriorIndex N → ℝ, (∀ i a, |b i a| ≤ M) →
      ∀ p : Fin (g.steps+1) → CartesianPhysicalState δ hδ N,
        AdjointEquation g.dt (fun i => cartesianPhysicalLaplacian o δ hδ N+
          PhysicalFiniteSpace.multiplier (b i)) p →
        ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps,
          ‖(cartesianPhysicalControlExtension o δ hδ N ω).adjoint (p i.castSucc)‖^2)+
          Real.exp (-2*d0*Smax)*‖p (Fin.last g.steps)‖^2) := by
  obtain ⟨c,l,β,qc,κ,h0,Δ0,CCE,_hc,hl,hβ,_hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCCE,hce⟩ :=
    box_cartesian_physical_load_carleman lo hi hpos hW hne hWS hω hinc ratio hratio
  obtain ⟨Cb,d0,hCb,hd0,hphysical⟩ := physical_observation_uniform_profiles.{0,0,0}
    2 β qc 1 CCE 1 1 hβ hqc (by norm_num) hCCE.le (by norm_num) (by norm_num)
  refine ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨C,hC,hdata⟩ := hphysical T M hT hM
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hdom h hh hh0' hlower hupper g hg hdt Smax hS hmesh hsmall hdtT b hb p hp
  let E := cartesianCountLpEquiv δ hδ N
  let ρh := cartesianInteriorCountProfile o δ N c (zero_le_one.trans hl)
  let V : Fin g.steps → CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N :=
    fun i => PhysicalFiniteSpace.multiplier (b i)
  let B := fun i => BoundedMultiplier.ofFinite (b i) M hM (hb i)
  have hload (w : TimeWeight) (hw : PhysicalQClass w g.period β qc) (hmax : w.max ≤ Smax) :
      (∀ i x, (ρh.multiplier w 0 (g.nodeTime i)).seminorm (E x) ≤
        1*(ρh.multiplier w 0 (g.nodeTime i)).seminorm (E x)) ∧
      PhysicalLoadCarleman ρh w g (cartesianPhysicalLaplacian o δ hδ N) E.toLinearMap
        (cartesianCountObservation o δ hδ N ω) E.symm.toLinearMap CCE := by
    refine ⟨fun _ _ => by rw [one_mul],?_⟩
    exact hce o δ hδ N hdom h hh hh0' hlower hupper g w hw hdt hmax
  have hnorm (x : CartesianPhysicalState δ hδ N) : ‖E x‖^2 = ‖x‖^2 := by
    rw [E.norm_map]
  have hobs := hdata (CartesianInteriorIndex N) Measure.count ℝ ρh rfl
    (cartesianInteriorCountProfile_negative o δ N c (zero_le_one.trans hl))
    (CartesianPhysicalState δ hδ N) g hg Smax hS hmesh hsmall hdtT
    (cartesianPhysicalLaplacian o δ hδ N) (cartesianPhysicalLaplacian_symmetric o δ hδ N)
    (cartesianPhysicalLaplacian_nonneg o δ hδ N) V
    (fun i => PhysicalFiniteSpace.multiplier_symmetric (b i))
    (fun i => PhysicalFiniteSpace.multiplier_opNorm_le (b i) M hM (hb i))
    E.toLinearMap E.toLinearMap (cartesianCountObservation o δ hδ N ω) E.symm.toLinearMap B
    (fun _ => le_rfl) (fun i x => PhysicalFiniteSpace.countLpEquiv_symm_map (B i) x)
    E.symm_apply_apply (fun x => by change ‖E x‖^2 ≤ 1*‖x‖^2; rw [hnorm,one_mul])
    (fun x => by change ‖x‖^2 ≤ 1*‖E x‖^2; rw [hnorm,one_mul]) hload p hp
  simpa only [cartesianCountObservation_norm] using hobs

end Carleman.Physical
