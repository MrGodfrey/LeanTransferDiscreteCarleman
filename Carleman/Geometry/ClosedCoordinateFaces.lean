module

public import Carleman.Geometry.CoordinateBoxChart
public import Mathlib.Topology.NhdsWithin

/-! Closed coordinate boxes and their actual closed faces, including edges.
The open transverse box is dense in the closed one when every side is positive. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def closedCoordinateBox (a b : Fin d → ℝ) : Set (SpatialCoordinates d) :=
  {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

theorem closure_openCoordinateBox (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j) :
    closure (openCoordinateBox a b)=closedCoordinateBox a b := by
  have he : openCoordinateBox a b =
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' (Set.pi univ (fun j => Ioo (a j) (b j))) := by
    ext x
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_Ioo,openCoordinateBox,mem_ofPred_eq]
    rfl
  rw [he,← Homeomorph.preimage_closure,closure_pi_set]
  have hcl (j : Fin d) : closure (Ioo (a j) (b j))=Icc (a j) (b j) := closure_Ioo (hpos j).ne
  simp_rw [hcl]
  ext x
  simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_Icc,closedCoordinateBox,mem_ofPred_eq]
  rfl

theorem coordinateFacePoint_continuous (i : Fin (d+1)) (c : ℝ) :
    Continuous (fun x : SpatialCoordinates d =>
      (WithLp.toLp 2 (i.insertNth c (fun j => x j)) : SpatialCoordinates (d+1))) := by
  have h := (coordinateBoxChart i 0).symm.continuous.comp (continuous_id.prodMk (continuous_const (y := c)))
  change Continuous (fun x : SpatialCoordinates d => (coordinateBoxChart i 0).symm (x,c)) at h
  simpa only [coordinateBoxChart_symm_apply,add_zero] using h

def coordinateClosedFace (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (upper : Bool) :
    Set (SpatialCoordinates (d+1)) :=
  closedCoordinateBox a b ∩ {y | y i=if upper then b i else a i}

theorem coordinateClosedFace_eq_image (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) :
    coordinateClosedFace i a b upper =
      (fun x : SpatialCoordinates d => WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j))) ''
        closedCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove) := by
  ext y
  constructor
  · rintro ⟨hy,he⟩
    refine ⟨WithLp.toLp 2 (fun j => y (i.succAbove j)),?_,?_⟩
    · exact fun j => hy (i.succAbove j)
    · apply PiLp.ext
      intro j
      induction j using Fin.succAboveCases i with
      | x => simpa only [Fin.insertNth_apply_same] using he.symm
      | p j => simp only [Fin.insertNth_apply_succAbove]
  · rintro ⟨x,hx,rfl⟩
    constructor
    · intro j
      induction j using Fin.succAboveCases i with
      | x =>
        simp only [Fin.insertNth_apply_same]
        cases upper <;> simp [hi.le]
      | p j => simpa only [Fin.insertNth_apply_succAbove,Function.comp_apply] using hx j
    · simp only [mem_ofPred_eq,Fin.insertNth_apply_same]

end Carleman
