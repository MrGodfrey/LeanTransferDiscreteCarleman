module

public import Carleman.Spatial.CoordinateReflectionH1

/-! Continuity of genuine reflection in the complete weak H1 graph topology. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem coordinateReflectionLp_continuous (r : Fin d) (c : ℝ) :
    Continuous (coordinateReflectionLp r c) :=
  (AddMonoidHomClass.isometry_of_norm (coordinateReflectionLp r c)
    (coordinateReflectionLp_norm r c)).continuous

theorem WeakSobolevJet.reflectCoordinate_tendsto (r : Fin d) (c : ℝ)
    {u : ℕ → WeakSobolevJet d 1 volume univ} {v : WeakSobolevJet d 1 volume univ}
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => reflectCoordinate r c (u n)) atTop (𝓝 (reflectCoordinate r c v)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  fin_cases k
  · change Tendsto (fun n => (OperatorMultiplier.const scalarZeroFiber).continuousLinearMap
      (coordinateReflectionLp r c (value (u n)))) atTop
      (𝓝 ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap (coordinateReflectionLp r c (value v))))
    exact ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap.continuous.tendsto _).comp
      (((coordinateReflectionLp_continuous r c).tendsto _).comp (valueCLM.continuous.tendsto v |>.comp hu))
  · change Tendsto (fun n => firstGradientAssembly (fun i => coordinateReflectionSign r i •
      coordinateReflectionLp r c (derivativeComponent (Sym.cons i Sym.nil) (field 1 (u n))))) atTop
      (𝓝 (firstGradientAssembly (fun i => coordinateReflectionSign r i •
        coordinateReflectionLp r c (derivativeComponent (Sym.cons i Sym.nil) (field 1 v)))))
    apply (firstGradientAssembly.continuous.tendsto _).comp
    apply tendsto_pi_nhds.mpr
    intro i
    exact (((coordinateReflectionLp_continuous r c).tendsto _).comp
      (((derivativeComponentCLM (Sym.cons i Sym.nil)).continuous.tendsto _).comp
        ((fieldCLM 1).continuous.tendsto v |>.comp hu))).const_smul _

end Carleman
