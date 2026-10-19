module

public import Carleman.Transfer.BoxHeatContinuous
public import Carleman.Transfer.CartesianTransportedData
public import Carleman.Transfer.HeatScaleUniform
public import Carleman.Spatial.BoxAnalyticData
public import Carleman.Geometry.BoxLipschitzDomain

/-! The full Cartesian heat estimate on a fixed box, with all analytic and numerical assumptions proved. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem box_cartesian_heat_estimate (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    {W ω : Set (SpatialCoordinates (d+1))} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ openCoordinateBox lo hi) (hω : IsOpen ω) (hinc : closure W ⊆ ω)
    (ratio : ℝ) (hratio : 1 ≤ ratio) :
    ∃ (c : SpatialCoordinates (d+1)) (l β qc κ h0 Δ0 C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox lo hi)) c (zero_le_one.trans hl)
      ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
        (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=openCoordinateBox lo hi)
        (h : ℝ), 0 < h → h ≤ h0 →
        (∀ j, h/ratio ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ (g : TimeGrid) (w : TimeWeight), IntervalQClass w.q g.period β qc → g.dt ≤ Δ0 →
        w.max ≤ κ*min (h^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) →
      let p := cartesianHeatGeometry (openCoordinateBox_isOpen lo hi) o δ hδ N ρ w W ω hW.measurableSet
      let r : Reconstruction (dirichletSubspace (openCoordinateBox lo hi)) (CartesianPhysicalState δ hδ N) :=
        hdom ▸ cartesianReconstruction o δ hδ N
      ∀ (s : Orientation) (z : g.Sequence (CartesianPhysicalState δ hδ N)),
        p.nodeEnergy g r z ≤ C *
          (g.weightedSq (p.node g p.state)
            (s.difference g z+g.map (cartesianPhysicalLaplacian o δ hδ N).toLinearMap z)+
            p.observationSq g (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap z) := by
  obtain ⟨c,l,β,qc,Cce,hc,hl,hβ,hβ1,hqc,hCce,hphase,hce⟩ :=
    box_heat_continuous_data.{0,0,0} lo hi hpos hW hne hWS
  let hS := openCoordinateBox_isOpen lo hi
  let hb := openCoordinateBox_isBounded lo hi
  let B := boundedDirichletOriginalForm hS (Nat.zero_lt_succ d) hb
  let hD := box_dirichlet_domain_le_h2 (Nat.zero_lt_succ d) lo hi hpos
  let ρ := interiorSpatialProfile (volume.restrict (openCoordinateBox lo hi)) c (zero_le_one.trans hl)
  have hρ : SmoothOnClosure ρ.value (openCoordinateBox lo hi) :=
    interiorCarlemanProfile_smoothOnClosure c l _
  have hρ2 : ContDiffOn ℝ 2 ρ.value (closure (openCoordinateBox lo hi)) :=
    ((interiorCarlemanProfile_contDiff c l).of_le (by norm_num)).contDiffOn
  obtain ⟨Creg,hCr,Ca,Ccomm,hCa,hCc,hreg,hallowed⟩ :=
    box_analytic_data_uniform (Nat.zero_lt_succ d) lo hi hpos ρ hρ
  obtain ⟨ε,hε,_he1,Ctime,hCt,Csuper,hCs,Capp,hCap,Cnum,hCn,hnum⟩ :=
    cartesian_numericalData_on hS (openCoordinateBox_convex lo hi) hb.isCompact_closure ρ hρ2
      ratio β 2 hratio hβ (by norm_num) W ω hW.measurableSet
      (hb.subset hWS).isCompact_closure hω hinc
  have hcover : max (CarlemanExponents.heat.dStar/2) (CarlemanExponents.heat.bStar/2) ≤ 2 := by
    rw [CarlemanExponents.heat_scale_exponents.1,CarlemanExponents.heat_scale_exponents.2.1]
    norm_num
  obtain ⟨κ0,h0,Δ0,Cfinal,hκ0,hh0,hh01,hΔ0,hΔ01,hCf,htransfer⟩ :=
    B.heat_scale_uniform (openCoordinateBox_bounded_lipschitz lo hi hpos) hD ρ hρ
      heatDifferentialFamily W hW.measurableSet Capp Creg (1/2) Ca Ccomm β 2 Ctime Csuper ε Cnum Cce
      hCap.le (by norm_num) (zero_le_one.trans hCa) hCc.le hβ (by norm_num)
      hCt.le hCs.le hε hCn.le hCce.le hcover hreg
  let κ := min κ0 ε
  have hκ : 0 < κ := lt_min hκ0 hε
  refine ⟨c,l,β,qc,κ,h0,Δ0,Cfinal,hc,hl,hβ,hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCf,hphase,?_⟩
  dsimp only
  intro o δ hδ N hdom h hh hh0' hlower hupper g w hq hdt hscale
  let r : Reconstruction (dirichletSubspace (openCoordinateBox lo hi)) (CartesianPhysicalState δ hδ N) :=
    hdom ▸ cartesianReconstruction o δ hδ N
  let L := cartesianLoadInterfaceOn o δ hδ N hdom
  have hL (f : CartesianPhysicalState δ hδ N) : L.Γ f = f :=
    cartesianLoadInterfaceOn_Γ o δ hδ N hdom f
  have hscale0 : w.max ≤ κ0*min (h^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) :=
    hscale.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (le_min (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg g.dt_pos.le _)))
  have hsx : w.max ≤ κ*h^(-(4/5:ℝ)) := hscale.trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hκ.le)
  have hsmall : h*w.max ≤ ε := by
    have hx := scale_monomial_le (p := (1:ℝ)) (ν := (1:ℝ)) hh (hh0'.trans hh01)
      (zero_le_one.trans w.max_ge_one) hκ.le (by norm_num) (by norm_num : (4/5:ℝ)*1 ≤ 1) hsx
    have hx' : h*w.max ≤ κ := by simpa only [Real.rpow_one] using hx
    exact hx'.trans (min_le_right κ0 ε)
  obtain ⟨ND⟩ := hnum o δ hδ N hdom h hh hlower hupper hD w g hq.toRegularity hsmall
  let state := fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value
  let control := fun t => cartesianControlSeminorm o δ hδ N ω (ρ.multiplier w 0 t).value
  let hdstate := cartesianHeatState_definite o δ hδ N ρ w
  let hdcontrol := cartesianHeatControl_definite o δ hδ N ω ρ w
  have hall := hallowed w 2
  have hcontinuous := hce (CartesianPhysicalState δ hδ N) (CartesianPhysicalState δ hδ N)
    (CartesianPhysicalControl o δ hδ N ω) state state control hdstate hdstate hdcontrol g w hq
  have ht := htransfer (CartesianPhysicalState δ hδ N) (CartesianPhysicalState δ hδ N)
    (CartesianPhysicalControl o δ hδ N ω) r (cartesianPhysicalLaplacian o δ hδ N).toLinearMap 0 L
    (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap state state control
    hdstate hdstate hdcontrol g w hq.toRegularity hall h (cartesianErrorScales Capp h hCap.le hh.le)
    hh hh0' hdt hscale0 (by simp only [cartesianErrorScales,CarlemanExponents.heat,pow_one,le_refl])
    (by simp only [cartesianErrorScales,CarlemanExponents.heat,mul_one,add_zero,le_refl]) ND hcontinuous
  intro s z
  exact ht.1 s (s.difference g z+g.map (cartesianPhysicalLaplacian o δ hδ N).toLinearMap z) z
    (by funext i; exact (hL _).symm)

end Carleman
