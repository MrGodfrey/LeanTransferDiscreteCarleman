module

public import Carleman.Geometry.CartesianInteriorVertex
public import Carleman.Spatial.CartesianKuhnPatchProjection
public import Carleman.Spatial.BoundedAffineSobolev
public import Carleman.Spatial.CartesianKuhnAffineMoment

/-! Exact affine reproduction by the genuine moment reconstruction,
with the physical boundary vertices kept explicitly in the statement. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnMoment_affine (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (a : CartesianInteriorIndex N) :
    cartesianKuhnMoment o δ hδ N
      (boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p) a =
      p (cartesianInteriorPoint o δ N a) := by
  unfold cartesianKuhnMoment
  have he := integral_congr_ae ((boundedAffineLp_ae (openCoordinateBox_isBounded o
    (fun j => o j+(N j:ℝ)*δ j)) p).mono (fun x hx => congrArg
      (fun r => r*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) hx))
  rw [he]
  exact cartesianKuhnHat_affine_moment o δ hδ N _ (cartesianInteriorPoint_mem o δ hδ N a) p

theorem cartesianKuhnProjection_affine_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (hp : ∀ k, (cartesianFiniteSimplex o δ hδ N i).points k ∉
      openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) → p ((cartesianFiniteSimplex o δ hδ N i).points k)=0)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnProjection o δ hδ N
      (boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p) x=p x := by
  classical
  let v := boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p
  change cartesianKuhnReconstruction o δ hδ N (cartesianKuhnMoment o δ hδ N v) x=p x
  rw [cartesianKuhnReconstruction_on_cell o δ hδ N _ i hx]
  have he : (fun k => cartesianInteriorData o δ N (cartesianKuhnMoment o δ hδ N v)
      ((cartesianFiniteSimplex o δ hδ N i).points k))=
      (fun k => p ((cartesianFiniteSimplex o δ hδ N i).points k)) := by
    funext k
    by_cases hk : (cartesianFiniteSimplex o δ hδ N i).points k ∈
      openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)
    · obtain ⟨a,ha⟩ := cartesianFiniteSimplex_interior_vertex o δ hδ N i k hk
      rw [← ha,cartesianInteriorData_at_node o δ hδ N]
      exact cartesianKuhnMoment_affine o δ hδ N p a
    · rw [cartesianInteriorData_zero_compl o δ hδ N _ hk,hp k hk]
  rw [he,simplexNodalInterpolant_reproduces]

theorem cartesianKuhnMoment_sub (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    cartesianKuhnMoment o δ hδ N (u-v)=cartesianKuhnMoment o δ hδ N u-cartesianKuhnMoment o δ hδ N v := by
  funext a
  have he := integral_congr_ae ((Lp.coeFn_sub u v).mono (fun x hx => congrArg
    (fun r => r*cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a) x) hx))
  simp only [cartesianKuhnMoment,Pi.sub_apply]
  rw [he]
  simp only [Pi.sub_apply,sub_mul]
  rw [integral_sub (cartesianKuhnMoment_integrable o δ hδ N u a)
    (cartesianKuhnMoment_integrable o δ hδ N v a),mul_sub]

theorem cartesianKuhnProjection_sub (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (x : SpatialCoordinates d) :
    cartesianKuhnProjection o δ hδ N (u-v) x=
      cartesianKuhnProjection o δ hδ N u x-cartesianKuhnProjection o δ hδ N v x := by
  simp only [cartesianKuhnProjection,cartesianKuhnReconstruction,cartesianKuhnMoment_sub,
    Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

end Carleman
