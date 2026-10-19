module

public import Carleman.Geometry.KuhnFaceMatching
public import Carleman.Spatial.BoxAllowedComparison

/-! The actual Cartesian cell geometry supplies a uniform comparison
of the original allowed weights under hq ≤ 1, including boundary vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem closedCoordinateBox_diameter_bound (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (L : ℝ) (hL : 0 ≤ L) (hupper : ∀ j, b j-a j ≤ L)
    {x y : SpatialCoordinates d} (hx : x ∈ closedCoordinateBox a b) (hy : y ∈ closedCoordinateBox a b) :
    dist x y ≤ (d:ℝ)*L := by
  rw [← closure_openCoordinateBox a b hpos] at hx hy
  have hb (z : SpatialCoordinates d) (hz : z ∈ openCoordinateBox a b) :
      closure (openCoordinateBox a b) ⊆ {t | dist t z ≤ (d:ℝ)*L} :=
    closure_minimal (fun t ht => coordinateBox_diameter_bound a b hpos L hL hupper t z ht hz)
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hc : closure (openCoordinateBox a b) ⊆ {z | dist x z ≤ (d:ℝ)*L} :=
    closure_minimal (fun z hz => hb z hz hx)
      (isClosed_le (continuous_const.dist continuous_id) continuous_const)
  exact hc hy

theorem cartesianKuhnSimplex_dist_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h)
    {x y : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (hy : y ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points) : dist x y ≤ (d:ℝ)*h := by
  apply closedCoordinateBox_diameter_bound (fun j => o j+(z j:ℝ)*δ j)
    (fun j => o j+((z j:ℝ)+1)*δ j) (fun j => by nlinarith [hδ j]) h hh.le
    (fun j => by nlinarith [hstep j])
  · exact cartesianKuhnSimplex_cell_subset_box o δ hδ z π hx
  · exact cartesianKuhnSimplex_cell_subset_box o δ hδ z π hy

theorem cartesianKuhn_allowedWeight_comparison (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) {S : Set (SpatialCoordinates d)}
    (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
    (ρ : SpatialProfile (volume.restrict S))
    (L : ℝ) (hL : 0 ≤ L)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) (hm : h*w.q t ≤ 1)
    (i : CartesianCellIndex N) {x y : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
    (hy : y ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    |((ρ.scaled η).multiplier w τ t).value x| ≤
      Real.exp (L*(d:ℝ))*((ρ.scaled η).multiplier w τ t).value y ∧
    ((ρ.scaled η).multiplier w τ t).value y ≤
      Real.exp (L*(d:ℝ))*|((ρ.scaled η).multiplier w τ t).value x| := by
  let M := cartesianKuhnPartition o δ hδ N
  have hb : |ρ.value x-ρ.value y| ≤ L*((d:ℝ)*h) :=
    (hρ x (closure_mono hTS (M.inside i hx)) y (closure_mono hTS (M.inside i hy))).trans
      (mul_le_mul_of_nonneg_left (cartesianKuhnSimplex_dist_le o δ hδ _ i.2 h hh hstep hx hy) hL)
  have he : Real.exp ((L*((d:ℝ)*h))*w.q t) ≤ Real.exp (L*(d:ℝ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (L*(d:ℝ))*(h*w.q t) := by ring
      _ ≤ (L*(d:ℝ))*1 := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := mul_one _
  rw [abs_of_pos (ρ.scaled_multiplier_pos η w τ t x)]
  constructor
  · exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb).trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t y).le)
  · have hb' : |ρ.value y-ρ.value x| ≤ L*((d:ℝ)*h) := by simpa only [abs_sub_comm] using hb
    exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb').trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t x).le)

end Carleman
