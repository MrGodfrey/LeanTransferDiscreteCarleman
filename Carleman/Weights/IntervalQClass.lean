module

public import Carleman.Weights.CellRegularity

/-! The manuscript's C² time weight assumptions on the original closed interval. -/
@[expose] public noncomputable section
open Set
namespace Carleman

/-- No regularity, positivity or periodicity outside the closed interval is required. -/
structure IntervalQClass (q : ℝ → ℝ) (T β qc : ℝ) : Prop where
  beta_pos : 0 < β
  qc_ge_one : 1 ≤ qc
  smooth : ContDiffOn ℝ 2 q (Icc 0 T)
  lower : ∀ t ∈ Icc 0 T, qc ≤ q t
  first_bound : ∀ t ∈ Icc 0 T, |derivWithin q (Icc 0 T) t| ≤ β*q t^2
  second_bound : ∀ t ∈ Icc 0 T,
    |derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) t| ≤ β^2*q t^3
  endpoint : q 0 = q T
  first_endpoint : derivWithin q (Icc 0 T) 0 = derivWithin q (Icc 0 T) T
  second_endpoint : derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) 0 =
    derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) T

def IntervalQClass.toRegularity {w : TimeWeight} {g : TimeGrid} {β qc : ℝ}
    (h : IntervalQClass w.q g.period β qc) : TimeWeightRegularity w g β :=
  TimeWeightRegularity.ofContDiffOn h.beta_pos h.smooth h.first_bound h.endpoint

end Carleman
