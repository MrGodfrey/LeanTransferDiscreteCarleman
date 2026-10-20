module

public import Carleman.Control.BochnerProductL2
public import Carleman.Control.AveragedPotentialWeakPairing

/-! The original time-cell average potential commutes with the actual Bochner-product reconstruction. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

theorem time_average_product_potential (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν))
    (u : Fin g.steps → Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (timeCellReconstruction g (fun i => (timeCellPotential g b i).map (u i)))=
      (timeReconstructedPotential g b).map (bochnerL2ProductIsometry (timeCellReconstruction g u)) := by
  classical
  apply Lp.ext
  have hm : ∀ᵐ x ∂ν, ∀ i, (timeCellPotential g b i).map (u i) x=
      (timeCellPotential g b i).value x*(u i) x := by
    apply eventually_all.mpr
    intro i
    filter_upwards [(timeCellPotential g b i).map_ae (u i)] with x hx
    exact hx
  filter_upwards [bochnerL2ProductIsometry_time_ae g (fun i => (timeCellPotential g b i).map (u i)),
    (timeReconstructedPotential g b).map_ae (bochnerL2ProductIsometry (timeCellReconstruction g u)),
    bochnerL2ProductIsometry_time_ae g u,Measure.quasiMeasurePreserving_snd.ae hm] with z hz hp hu hmz
  rw [hz,hp,hu,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z.1 ∈ g.physicalTimeCell i
  · rw [indicator_of_mem (show z ∈ Prod.fst ⁻¹' g.physicalTimeCell i from hi),
      indicator_of_mem (show z ∈ Prod.fst ⁻¹' g.physicalTimeCell i from hi),
      timeReconstructedPotential_on_cell g b i hi]
    exact hmz i
  · simp only [mem_preimage,hi,not_false_eq_true,indicator_of_notMem,mul_zero]

def fixedTimeCellPotential (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν))
    (i : Fin g.steps) : BoundedMultiplier ν := by
  subst T
  exact timeCellPotential g b i

theorem fixedTimeCellPotential_bound (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) (i : Fin g.steps) :
    (fixedTimeCellPotential T g hT b i).bound=b.bound := by
  subst T
  exact timeCellPotential_bound g b i

theorem fixed_time_average_product_potential (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν))
    (u : Fin g.steps → Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
      (fun i => (fixedTimeCellPotential T g hT b i).map (u i)))=
      (fixedTimePotential T g hT b).map (bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT u)) := by
  subst T
  exact time_average_product_potential g b u

theorem fixedTimeCellPotential_value (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) (i : Fin g.steps) (x : Ω) :
    (fixedTimeCellPotential T g hT b i).value x=g.dt⁻¹*∫ t in g.physicalTimeCell i, b.value (t,x) := by
  subst T
  exact timeCellPotential_value g b i x

theorem time_average_reconstructed_weak_pairing [IsFiniteMeasure ν]
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b φ : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν))
    (u v : ∀ n, Fin (g n).steps → Lp ℝ 2 ν)
    (Y : Lp (Lp ℝ 2 ν) 2 (volume.restrict (Ioc 0 T))) {C : ℝ}
    (hu : ∀ n, ‖fixedTimeCellReconstruction T (g n) (hT n) (u n)‖ ≤ C)
    (hweak : ∀ w, Tendsto (fun n => inner ℝ
      (fixedTimeCellReconstruction T (g n) (hT n) (u n)) w) atTop (𝓝 (inner ℝ Y w)))
    (hv : Tendsto (fun n => bochnerL2ProductIsometry
      (fixedTimeCellReconstruction T (g n) (hT n) (v n))) atTop (𝓝 φ.toL2)) :
    Tendsto (fun n => inner ℝ
      (fixedTimeCellReconstruction T (g n) (hT n)
        (fun i => (fixedTimeCellPotential T (g n) (hT n) b i).map (u n i)))
      (fixedTimeCellReconstruction T (g n) (hT n) (v n))) atTop
      (𝓝 (inner ℝ (b.map (bochnerL2ProductIsometry Y)) φ.toL2)) := by
  have hh := timeAveragedPotential_weak_pairing T hTpos g hT htlim b φ
    (fun n => bochnerL2ProductIsometry (fixedTimeCellReconstruction T (g n) (hT n) (u n)))
    (fun n => bochnerL2ProductIsometry (fixedTimeCellReconstruction T (g n) (hT n) (v n)))
    (bochnerL2ProductIsometry Y)
    (fun n => by simpa only [LinearIsometry.norm_map] using hu n)
    (bochnerL2ProductIsometry_weak _ Y hweak) hv
  simpa only [← fixed_time_average_product_potential,LinearIsometry.inner_map_map] using hh

end Carleman
