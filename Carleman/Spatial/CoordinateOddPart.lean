module

public import Carleman.Spatial.CoordinateReflectionLp

/-! Actual odd parts and their local symmetry under commuting face reflections. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem coordinateReflection_commute (r s : Fin d) (c e : ℝ) (hrs : r ≠ s)
    (x : SpatialCoordinates d) :
    coordinateReflection r c (coordinateReflection s e x)=
      coordinateReflection s e (coordinateReflection r c x) := by
  ext j
  simp only [coordinateReflection_apply]
  by_cases hjr : j=r
  · subst j; simp [hrs]
  · by_cases hjs : j=s
    · subst j; simp [Ne.symm hrs]
    · simp [hjr,hjs]

def coordinateOddPart (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  u-coordinateReflectionLp r c u

theorem coordinateOddPart_ae (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    coordinateOddPart r c u =ᵐ[volume] fun x => u x-u (coordinateReflection r c x) := by
  filter_upwards [Lp.coeFn_sub u (coordinateReflectionLp r c u),
    coordinateReflectionLp_ae r c u] with x hx hy
  change (u-coordinateReflectionLp r c u) x=_
  rw [hx,Pi.sub_apply,hy,Function.comp_apply]

def IsOddInSlab (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (r : Fin d) (c δ : ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
    |x r-c|<δ → u (coordinateReflection r c x)= -u x

theorem coordinateOddPart_odd (r : Fin d) (c δ : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    IsOddInSlab (coordinateOddPart r c u) r c δ := by
  filter_upwards [coordinateOddPart_ae r c u,
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae
      (coordinateOddPart_ae r c u)] with x hx hy
  intro _
  rw [hx,hy,coordinateReflection_involutive]
  ring

theorem IsOddInSlab.oddPart_other {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {r : Fin d} {c δ : ℝ} (h : IsOddInSlab u r c δ)
    (s : Fin d) (e : ℝ) (hrs : r ≠ s) :
    IsOddInSlab (coordinateOddPart s e u) r c δ := by
  filter_upwards [h,(coordinateReflection_measurePreserving s e).quasiMeasurePreserving.ae h,
    coordinateOddPart_ae s e u,
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae
      (coordinateOddPart_ae s e u)] with x hx hy hz hw
  intro hxc
  have hs : |(coordinateReflection s e x) r-c|<δ := by
    simpa only [coordinateReflection_apply,ite_eq_right hrs] using hxc
  rw [hw,hz,← coordinateReflection_commute r s c e hrs,hx hxc,hy hs]
  ring

end Carleman
