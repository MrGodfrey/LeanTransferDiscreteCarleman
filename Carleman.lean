module

public import Carleman.Transfer.WeightedTestTime
public import Carleman.Transfer.SpatialCea
public import Carleman.Spatial.SquaredWeightTest
public import Carleman.Section4.SpatialEnergy
public import Carleman.Periodic.SeminormSum
public import Carleman.Section4.NodalApproximation

public import Carleman.Periodic.OperatorEnergy
public import Carleman.Periodic.TestOperatorDerivative
public import Carleman.Transfer.SpatialConsistency
public import Carleman.Transfer.SpatialDuality
public import Carleman.Transfer.DiscreteExistence
public import Carleman.Spatial.WeightedEnergySeminorm
public import Carleman.Periodic.SeminormAlgebra

public import Carleman.Periodic.Telescoping
public import Carleman.Periodic.SummationByParts
public import Carleman.Transfer.Residual
public import Carleman.Transfer.Adjoint
public import Carleman.Transfer.Conditional

public import Carleman.Weights.CellLemma
public import Carleman.Transfer.ConcreteNorms
public import Carleman.Transfer.ShiftNorm

public import Carleman.Weights.SpatialDerivatives
public import Carleman.Weights.TemporalDerivatives
public import Carleman.Transfer.SobolevGeometry

public import Carleman.Transfer.SobolevBridges
public import Carleman.Weights.SpatialProduct
public import Carleman.Weights.TemporalPerturbation

public import Carleman.Periodic.SobolevEuler

public import Carleman.Continuous.ClassicalWeakTime
public import Carleman.Continuous.EulerTimeEmbedding
public import Carleman.Continuous.FiniteHarmonic
public import Carleman.Continuous.FormTimeGraph
public import Carleman.Continuous.FrequencyEnergy
public import Carleman.Continuous.FrequencySolve
public import Carleman.Continuous.HarmonicTrajectory
public import Carleman.Continuous.L2Pairing
public import Carleman.Continuous.PeriodicEvolution
public import Carleman.Continuous.PeriodicGraphEquivalence
public import Carleman.Continuous.PeriodicGraphSpace
public import Carleman.Continuous.TimeInterval
public import Carleman.Continuous.WeakTimeSpace

-- T009: genuine arbitrary-load periodic well-posedness and time graph estimates.
public import Carleman.Continuous.ConstantPeriodicExistence
public import Carleman.Continuous.FrozenContinuousGraph
public import Carleman.Continuous.HarmonicDensity
public import Carleman.Continuous.PeriodicSolutionOperator
public import Carleman.Continuous.RegularTimeCore
public import Carleman.Continuous.ShiftedContinuousGraph
public import Carleman.Continuous.TimeGraphBound
public import Carleman.Continuous.TimeGraphEnergy
public import Carleman.Continuous.TimeTestPrimitive
public import Carleman.Continuous.TimeTraceBound
public import Carleman.Continuous.VariablePeriodicExistence
public import Carleman.Continuous.VariableTimeEnergy
public import Carleman.Continuous.WeakPeriodicUnique
public import Carleman.Continuous.WeakTimeConstant
public import Carleman.Continuous.WeakTimeEnergy
public import Carleman.Continuous.WeakTimeFTC
public import Carleman.Continuous.WeakTimePrimitive
public import Carleman.Transfer.FrozenExistence

-- T010: full spatial weak Leibniz, uniform conjugation and original shifted forms.
public import Carleman.Spatial.CommutatorPerturbation
public import Carleman.Spatial.ComponentNorms
public import Carleman.Spatial.CoordinateWords
public import Carleman.Spatial.LeibnizBounds
public import Carleman.Spatial.MultiplierAlgebra
public import Carleman.Spatial.ParameterConjugation
public import Carleman.Spatial.ShiftedFormBounds
public import Carleman.Spatial.SmoothMultipliers
public import Carleman.Spatial.WeakLeibniz
public import Carleman.Spatial.WeightedSobolevNorm
public import Carleman.Weights.AllowedFormBounds
public import Carleman.Weights.ConformingConjugation
public import Carleman.Weights.SmoothClosure
public import Carleman.Weights.SobolevConjugation

-- T011: genuine weak time products and Bochner graph conjugation.
public import Carleman.Continuous.BochnerNorm
public import Carleman.Continuous.GraphMeasurability
public import Carleman.Continuous.WeakTimeProduct
public import Carleman.Spatial.ExponentialDerivative
public import Carleman.Spatial.SobolevMeasurability
public import Carleman.Spatial.SobolevTimeGraph
public import Carleman.Weights.SobolevGraphRegularity
public import Carleman.Weights.SpacetimeCommutator
public import Carleman.Weights.SpacetimeConjugation
public import Carleman.Weights.TemporalMultiplier
public import Carleman.Weights.WeakConjugationIdentity
public import Carleman.Weights.WeakTemporalProduct
public import Carleman.Weights.WeightedOperatorRegularity
public import Carleman.Weights.WeightedWeakTrajectory

-- T012: actual affine reconstruction and uniform temporal errors.
public import Carleman.Continuous.AffineTimeClass
public import Carleman.Continuous.FormEnergyClass
public import Carleman.Continuous.TemporalEnergyError
public import Carleman.Continuous.TemporalErrorIdentity
public import Carleman.Continuous.TemporalL2Error
public import Carleman.Continuous.TemporalWeakError
public import Carleman.Continuous.TimeAdjoint
public import Carleman.Continuous.WeakTimePairing
public import Carleman.Periodic.AffineReconstruction

-- T013: intrinsic closure smoothness, actual space-time N and weighted operator energy.
public import Carleman.Spatial.IntrinsicMultipliers
public import Carleman.Spatial.SpacetimeWeightedNorm
public import Carleman.Spatial.WeightedOperatorEnergy
public import Carleman.Weights.AllowedOperatorEnergy
public import Carleman.Weights.ClosureConforming
public import Carleman.Weights.ClosureProfile
public import Carleman.Weights.ClosureSpacetime
public import Carleman.Weights.ClosureSpacetimeEnergy
public import Carleman.Weights.ClosureWeakTrajectory
public import Carleman.Weights.IntrinsicConjugation
public import Carleman.Weights.IntrinsicDerivatives
public import Carleman.Weights.IntrinsicSmoothClosure

-- T014: frozen error energy and full-space weak parameter interpolation.
public import Carleman.Continuous.BochnerNormAlgebra
public import Carleman.Continuous.FrozenErrorResidual
public import Carleman.Spatial.ConvolutionL2
public import Carleman.Spatial.DiscreteMaximum
public import Carleman.Spatial.FullSpaceInterpolation
public import Carleman.Spatial.FullSpaceJetInterpolation
public import Carleman.Spatial.LowerShiftEnergy
public import Carleman.Spatial.MollifiedInterpolation
public import Carleman.Spatial.RealL2Integral
public import Carleman.Spatial.WeakConvolution
public import Carleman.Weights.FrozenErrorEnergy
public import Carleman.Weights.FrozenOperatorEnergy
public import Carleman.Weights.FrozenShiftLower

-- T015: actual weighted temporal duality and frozen graph remainders.
public import Carleman.Continuous.WeightedTemporalDuality
public import Carleman.Periodic.AffineSeminorm
public import Carleman.Weights.FrozenTemporalPerturbation
public import Carleman.Weights.TimeL2Multiplier
public import Carleman.Weights.WeightedAdjointRemainder
public import Carleman.Weights.WeightedAffineDefect
public import Carleman.Weights.WeightedGraphCommutator
public import Carleman.Weights.WeightedGraphConstruction
public import Carleman.Weights.WeightedGraphRemainder

-- T016: actual weighted Euler graphs and closed second-order temporal rates.
public import Carleman.Continuous.NormDomination
public import Carleman.Continuous.WeightedGraphErrorNorm
public import Carleman.Periodic.L2Algebra
public import Carleman.Spatial.EnergyLowOrderAbsorption
public import Carleman.Spatial.SecondOrderCommutatorEnergy
public import Carleman.Spatial.SecondOrderParameterGraph
public import Carleman.Spatial.SecondOrderWeightData
public import Carleman.Weights.EulerTemporalPerturbation
public import Carleman.Weights.SecondOrderEulerGraph
public import Carleman.Weights.SecondOrderEulerSobolev
public import Carleman.Weights.SecondOrderFrozenGraph
public import Carleman.Weights.SecondOrderTemporalError
public import Carleman.Weights.SecondOrderTemporalL2
public import Carleman.Weights.WeightedEulerRemainder

-- T017: explicit higher-order interpolation chain and Lipschitz inward-cone geometry.
public import Carleman.Geometry.LipschitzInwardCone
public import Carleman.Spatial.AllowedWeightData
public import Carleman.Spatial.DomainParameterInterpolation
public import Carleman.Spatial.InterpolatedCommutator
public import Carleman.Spatial.InterpolatedParameterGraph
public import Carleman.Weights.InterpolatedEulerGraph
public import Carleman.Weights.InterpolatedEulerSobolev
public import Carleman.Weights.InterpolatedFrozenGraph
public import Carleman.Weights.InterpolatedTemporalError
public import Carleman.Weights.InterpolatedTemporalL2

public import Carleman.Geometry.InteriorErosion
public import Carleman.Geometry.InwardConeTube
public import Carleman.Geometry.LocalLipschitzCharts
public import Carleman.Spatial.ConeCoordinateInterpolation
public import Carleman.Spatial.DiscreteInterpolation
public import Carleman.Spatial.DomainConvolution
public import Carleman.Spatial.DomainCoordinateInterpolation
public import Carleman.Spatial.DomainJetInterpolation
public import Carleman.Spatial.DomainJetNeighbor
public import Carleman.Spatial.JetDirections
public import Carleman.Spatial.L2Averaging
public import Carleman.Spatial.L2FiniteCover
public import Carleman.Spatial.LipschitzDomainParameterInterpolation
public import Carleman.Spatial.LocalMollifierLimit
public import Carleman.Spatial.MollifiedConeFTC
public import Carleman.Spatial.MollifiedConeInterpolation
public import Carleman.Spatial.MollifiedConeTranslation
public import Carleman.Spatial.WeakConeInterpolation
public import Carleman.Spatial.WeakDirections
public import Carleman.Spatial.ZeroExtensionLp
public import Carleman.Weights.LipschitzEulerSobolev
public import Carleman.Weights.LipschitzFrozenSobolev
public import Carleman.Weights.LipschitzTemporalError
public import Carleman.Weights.InterpolatedFrozenSobolev

public import Carleman.Section3.AllowedFamily
public import Carleman.Section3.Complete
public import Carleman.Section3.ContinuousInterval
public import Carleman.Section3.OriginalBilinear
public import Carleman.Section3.OriginalForm
public import Carleman.Section3.OriginalOperator
public import Carleman.Section3.OriginalWeights
public import Carleman.Section3.ProfileUniform
public import Carleman.Section3.SignedUniform
public import Carleman.Section3.SolvedProfiles
public import Carleman.Section3.Statements
public import Carleman.Section3.WeakSolutions
public import Carleman.Weights.InterpolatedShiftGraph
public import Carleman.Weights.InterpolatedShiftSobolev
public import Carleman.Weights.LipschitzShiftSobolev
public import Carleman.Weights.ShiftedGraphRemainder

public import Carleman.Section4.ApproximationData
public import Carleman.Section4.EnergyRate
public import Carleman.Section4.TestData
public import Carleman.Section4.EnergyEstimate
public import Carleman.Section4.EnergyUniform
public import Carleman.Section4.DualityBound
public import Carleman.Section4.L2Estimate
public import Carleman.Section4.SpatialUniform

public import Carleman.Spatial.SpacetimeNormAlgebra
public import Carleman.Spatial.SpacetimeCellEnergy
public import Carleman.Section4.CombinedEstimate
public import Carleman.Section4.CombinedUniform

public import Carleman.Transfer.CombinedNorms
public import Carleman.Transfer.CombinedErrors
public import Carleman.Transfer.CompleteBridges
public import Carleman.Transfer.OriginalData
public import Carleman.Transfer.OriginalUniform

public import Carleman.Transfer.ScaleExponents
public import Carleman.Transfer.ScalePowers
public import Carleman.Transfer.ScaleRates
public import Carleman.Transfer.ScaleBudgets
public import Carleman.Transfer.ScaleSmallness
public import Carleman.Transfer.ScaleUniform
public import Carleman.Transfer.HeatScaleUniform

public import Carleman.Control.FiniteResolvent
public import Carleman.Control.PhysicalSolutions
public import Carleman.Control.PhysicalDuality
public import Carleman.Control.PhysicalEnergy
public import Carleman.Control.PhysicalEquations
public import Carleman.Control.PhysicalLemma

public import Carleman.Control.RayleighStep
public import Carleman.Control.PositiveResolvent
public import Carleman.Control.ReverseIteration
public import Carleman.Control.FilterReverse

public import Carleman.Control.PhysicalFlow
public import Carleman.Control.PenalizedHUM
public import Carleman.Control.PhysicalHUM
public import Carleman.Control.RelaxedControl

public import Carleman.Control.PhysicalCutoff
public import Carleman.Control.PhysicalWeight
public import Carleman.Control.PhysicalWeightSecond
public import Carleman.Control.PhysicalRamp
public import Carleman.Control.PhysicalWindow
public import Carleman.Control.PhysicalWeightLocalization
public import Carleman.Control.PhysicalCutoffEnergy
public import Carleman.Control.PhysicalParameterChoice
