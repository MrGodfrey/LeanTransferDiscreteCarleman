module

public import Carleman.Spatial.CoordinateOddPart
public import Carleman.Spatial.ZeroExtensionLp
public import Carleman.Geometry.CoordinateBoxConvexity

/-! Both original faces retain local oddness after the two actual reflections. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def IsZeroOutsideSlab (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (r : Fin d) (a b : ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), x r ∉ Ioo a b → u x=0

theorem zeroExtend_box_zero_outside_slab (a b : Fin d → ℝ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (r : Fin d) :
    IsZeroOutsideSlab (zeroExtendLp (openCoordinateBox_isOpen a b).measurableSet u)
      r (a r) (b r) := by
  filter_upwards [zeroExtendLp_ae (openCoordinateBox_isOpen a b).measurableSet u] with x hx
  intro h
  have hn : x ∉ openCoordinateBox a b := fun hxS => h (hxS r)
  rw [hx,indicator_of_notMem hn]

theorem IsZeroOutsideSlab.lower_oddPart
    {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {r : Fin d} {a b : ℝ} (hab : a < b) (h : IsZeroOutsideSlab u r a b) :
    IsZeroOutsideSlab (coordinateOddPart r a u) r (2*a-b) b := by
  filter_upwards [h,(coordinateReflection_measurePreserving r a).quasiMeasurePreserving.ae h,
    coordinateOddPart_ae r a u] with x hx hy hz
  intro hn
  have h1 : x r ∉ Ioo a b := by
    intro hi; apply hn; constructor <;> linarith [hi.1,hi.2]
  have h2 : (coordinateReflection r a x) r ∉ Ioo a b := by
    simp only [coordinateReflection_apply,ite_true]
    intro hi; apply hn; constructor <;> linarith [hi.1,hi.2]
  rw [hz,hx h1,hy h2,sub_self]

theorem IsZeroOutsideSlab.double_oddPart_lower
    {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {r : Fin d} {a b : ℝ} (hab : a < b) (h : IsZeroOutsideSlab u r a b) :
    IsOddInSlab (coordinateOddPart r b (coordinateOddPart r a u)) r a (b-a) := by
  let v := coordinateOddPart r a u
  have hv : IsZeroOutsideSlab v r (2*a-b) b := h.lower_oddPart hab
  have ho := coordinateOddPart_odd r a (b-a) u
  filter_upwards [coordinateOddPart_ae r b v,
    (coordinateReflection_measurePreserving r a).quasiMeasurePreserving.ae
      (coordinateOddPart_ae r b v),ho,
    (coordinateReflection_measurePreserving r b).quasiMeasurePreserving.ae hv,
    (coordinateReflection_measurePreserving r a).quasiMeasurePreserving.ae
      ((coordinateReflection_measurePreserving r b).quasiMeasurePreserving.ae hv)]
    with x hx hy hz h1 h2
  intro hxc
  have hlt := abs_lt.mp hxc
  have hn1 : (coordinateReflection r b x) r ∉ Ioo (2*a-b) b := by
    simp only [coordinateReflection_apply,ite_true]
    intro hi; linarith [hi.2,hlt.2]
  have hn2 : (coordinateReflection r b (coordinateReflection r a x)) r ∉ Ioo (2*a-b) b := by
    simp only [coordinateReflection_apply,ite_true]
    intro hi; linarith [hi.2,hlt.1]
  have hz' : v (coordinateReflection r a x)= -v x := hz hxc
  rw [hy,hx,h1 hn1,h2 hn2,sub_zero,sub_zero]
  exact hz'

theorem double_oddPart_both_faces
    {u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    {r : Fin d} {a b : ℝ} (hab : a < b) (h : IsZeroOutsideSlab u r a b) :
    IsOddInSlab (coordinateOddPart r b (coordinateOddPart r a u)) r a (b-a) ∧
      IsOddInSlab (coordinateOddPart r b (coordinateOddPart r a u)) r b (b-a) :=
  ⟨h.double_oddPart_lower hab,coordinateOddPart_odd r b (b-a) _⟩

end Carleman
