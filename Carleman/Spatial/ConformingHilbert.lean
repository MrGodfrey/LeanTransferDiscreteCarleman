module

public import Carleman.Spatial.SobolevHilbert
public import Carleman.Continuous.CoerciveForm

/-! The original conforming V, with its actual weak Sobolev Hilbert topology.
Closedness is in H^m, not in H. The zero-order embedding has range exactly V. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)} (V : Submodule ℝ (Lp ℝ 2 ν))

def conformingHilbert : Submodule ℝ (SobolevHilbert d m ν S) :=
  V.comap SobolevHilbert.value.toLinearMap

def conformingEmbed : conformingHilbert (m := m) (S := S) V →L[ℝ] Lp ℝ 2 ν :=
  SobolevHilbert.value.comp (conformingHilbert (m := m) (S := S) V).subtypeL

/-- This is exactly original A1 closedness of V in the Sobolev energy norm. -/
theorem conformingHilbert_isClosed
    (hc : IsClosed {u : WeakSobolevJet d m ν S | WeakSobolevJet.value u ∈ V}) :
    IsClosed (conformingHilbert (m := m) (S := S) V : Set (SobolevHilbert d m ν S)) :=
  hc.preimage SobolevHilbert.toJet.continuous

theorem conformingHilbert_completeSpace
    (hc : IsClosed {u : WeakSobolevJet d m ν S | WeakSobolevJet.value u ∈ V}) :
    CompleteSpace (conformingHilbert (m := m) (S := S) V) := by
  let : IsClosed (conformingHilbert (m := m) (S := S) V : Set (SobolevHilbert d m ν S)) :=
    conformingHilbert_isClosed V hc
  exact IsClosed.completeSpace_coe

/-- No boundary or conforming states are lost by the Hilbert realization. -/
theorem conformingEmbed_range (hV : V ≤ sobolevSubspace d m ν S) :
    (conformingEmbed (m := m) (S := S) V).toLinearMap.range = V := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.property
  · intro hx
    obtain ⟨j, hj⟩ := hV hx
    refine ⟨⟨SobolevHilbert.ofJet j, ?_⟩, ?_⟩
    · change WeakSobolevJet.value j ∈ V
      rwa [hj]
    · exact hj

theorem conformingEmbed_dense (hV : V ≤ sobolevSubspace d m ν S) (hd : Dense (V : Set (Lp ℝ 2 ν))) :
    DenseRange (conformingEmbed (m := m) (S := S) V) := by
  change Dense (Set.range (conformingEmbed (m := m) (S := S) V))
  change Dense ((conformingEmbed (m := m) (S := S) V).toLinearMap.range : Set (Lp ℝ 2 ν))
  rwa [conformingEmbed_range V hV]

variable [IsLocallyFiniteMeasure ν] (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)

include hS hν in
theorem conformingEmbed_injective : Function.Injective (conformingEmbed (m := m) (S := S) V) :=
  (SobolevHilbert.value_injective hS hν).comp Subtype.val_injective

/-- Original continuous symmetric coercive form on V, now on a genuine
Hilbert realization. No resolvent, evolution solution or graph estimate is input. -/
def conformingCoerciveForm (hV : V ≤ sobolevSubspace d m ν S) (hd : Dense (V : Set (Lp ℝ 2 ν)))
    (a : conformingHilbert (m := m) (S := S) V →L[ℝ]
      conformingHilbert (m := m) (S := S) V →L[ℝ] ℝ)
    (hsym : ∀ u v, a u v = a v u) (hcoer : ∃ c > (0 : ℝ), ∀ u, c*‖u‖*‖u‖ ≤ a u u) :
    CoerciveForm (Lp ℝ 2 ν) (conformingHilbert (m := m) (S := S) V) where
  embed := conformingEmbed V
  injective := conformingEmbed_injective V hS hν
  dense := conformingEmbed_dense V hV hd
  form := a
  symmetric := hsym
  coercive := hcoer

end Carleman
