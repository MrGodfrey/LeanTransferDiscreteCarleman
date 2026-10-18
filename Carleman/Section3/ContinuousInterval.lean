module

public import Carleman.Section3.Complete

/-! Period-only entrypoint for the nonfrozen problem. The internal TimeGrid
carrier packages the interval already used by the Bochner Sobolev machinery;
no cells, nodal coefficients or mesh condition occur in this theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

def periodCarrier (T : ℝ) (hT : 0 < T) : TimeGrid := ⟨1,by omega,T,hT⟩

@[simp] theorem periodCarrier_period (T : ℝ) (hT : 0 < T) : (periodCarrier T hT).period = T := by
  simp [periodCarrier,TimeGrid.period]

theorem periodCarrier_measure (T : ℝ) (hT : 0 < T) :
    (periodCarrier T hT).timeMeasure = volume.restrict (Ioo 0 T) := by
  simp [TimeGrid.timeMeasure]

/-- The original C² assumptions supply the weaker first-derivative data used
by the proof. Extra original endpoint/second derivative bounds need not be added. -/
def intervalWeightRegularity {T β : ℝ} (hT : 0 < T) (w : TimeWeight)
    (hβ : 0 < β) (hc : ContDiffOn ℝ 2 w.q (Icc 0 T))
    (hb : ∀ t ∈ Icc 0 T, |derivWithin w.q (Icc 0 T) t| ≤ β*w.q t^2)
    (he : w.q 0 = w.q T) : TimeWeightRegularity w (periodCarrier T hT) β :=
  TimeWeightRegularity.ofContDiffOn hβ (by simpa using hc) (by simpa using hb) (by simpa using he)

namespace Section3

/-- The common restriction with delta≤1 includes the manuscript's dt≤1. -/
theorem mesh_dt_le_one {g : TimeGrid} {w : TimeWeight} {δ : ℝ}
    (hδ : δ ≤ 1) (hmesh : g.dt*w.max^2 ≤ δ) : g.dt ≤ 1 := by
  have hp : 1 ≤ w.max^2 := one_le_pow₀ w.max_ge_one
  have hh := mul_le_mul_of_nonneg_left hp g.dt_pos.le
  rw [mul_one] at hh
  exact hh.trans (hmesh.trans hδ)

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  {b : CoerciveForm (Lp ℝ 2 ν) W}
  {V : Submodule ℝ (Lp ℝ 2 ν)} {hV : V ≤ sobolevSubspace d m ν S}
  {hDV : b.domain ≤ V} {hD : b.domain ≤ sobolevSubspace d (2*m) ν S}
  {a : V → V → ℝ} {ρ : SpatialProfile ν} {c C Ccomm β τStar K δ : ℝ} {L₀ : ℝ → ℝ}

/-- Lemma 3.1 on every T>0, with actual μ(t)=(Lq(t))^(2m) and no step condition.
Existence, uniqueness, jet MemLp and the full weighted R estimate are included. -/
theorem Conclusions.primitive_on_interval
    (H : Conclusions hS hν b hV hDV hD a ρ c C Ccomm β τStar K L₀ δ)
    (B : ℝ) (hB : 0 < B) (T : ℝ) (hT : 0 < T) (s : Orientation)
    (w : TimeWeight) (hc : ContDiffOn ℝ 2 w.q (Icc 0 T))
    (hβ : 0 < β) (hb : ∀ t ∈ Icc 0 T, |derivWithin w.q (Icc 0 T) t| ≤ β*w.q t^2)
    (he : w.q 0 = w.q T) (L τ : ℝ) (e : Bool) (hL : L₀ B ≤ L) (hτ : |τ| ≤ τStar)
    (ha : AllowedFamily hS hν hV hD a b.operator ρ w c C Ccomm τStar) :
    let h := intervalWeightRegularity hT w hβ hc hb he
    let hpos : 0 < L := zero_lt_one.trans_le ((H.threshold B hB).trans hL)
    ContinuousEstimate hS hν b hD (periodCarrier T hT) s w (ρ.signed e) τ K
      h.aestronglyMeasurable (h.shiftMultiplier m L hpos) :=
  H.primitive B hB _ s w _ L τ e hL hτ ha _
end Section3
end Carleman
