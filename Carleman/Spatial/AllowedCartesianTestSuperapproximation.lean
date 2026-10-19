module

public import Carleman.Weights.PrescribedNodalSuperapproximation
public import Carleman.Geometry.CartesianKuhnShape
public import Carleman.Spatial.AllowedCartesianDiagonalTest

/-! The original Cartesian test superapproximation, for every discrete state.
The fixed physical domain determines the constants before any mesh or weight
is chosen. The residual has exactly the sign in eq:testsuper. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem allowed_weight_cartesian_test_superapproximation
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ ε > (0:ℝ), ∃ C > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ ε →
    ∀ f : CartesianInteriorIndex N → ℝ,
    ∃ e : WeakSobolevJet d 1
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hdom.le)
      let ξ := (((ρ.scaled (-η)).multiplier w (-τ) t).onSubdomain hdom.le)
      WeakSobolevJet.value e=
        cartesianKuhnReconstructionLp o δ hδ N (cartesianSquaredWeightTest o δ N σ.value f)-
          (σ.mul σ).map (cartesianKuhnReconstructionLp o δ hδ N f) ∧
      WeakSobolevJet.weightedNorm (w.q t) ξ e ≤
        C*h*w.max*WeakSobolevJet.weightedNorm (w.q t) σ
          (cartesianKuhnReconstructionJet o δ hδ N f) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using (hcompact.isBounded.subset subset_closure).measure_lt_top (μ := volume)⟩
  obtain ⟨K,hK,hballs⟩ := cartesianKuhn_uniform_inballs (d := d) κ hκ
  obtain ⟨C,hC,hbound⟩ := allowed_prescribed_nodal_superapproximation hS hc hcompact ρ hρ hK.le
  refine ⟨1/(d+1:ℝ),by positivity,C*(d+1:ℝ),by positivity,?_⟩
  intro o δ hδ N hdom h hh hlower hupper w τ t η hη hsmall f
  subst S
  let M := cartesianKuhnPartition o δ hδ N
  let u := cartesianKuhnReconstructionJet o δ hδ N f
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  have hD := cartesianKuhn_maxDiameter_le o δ hδ N h hh hupper
  have hmesh : M.maxDiameter*w.q t ≤ 1 := by
    calc
      _ ≤ ((d+1:ℝ)*h)*w.q t := mul_le_mul_of_nonneg_right hD (w.nonneg t)
      _ = (d+1:ℝ)*(h*w.q t) := by ring
      _ ≤ (d+1:ℝ)*(1/(d+1:ℝ)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 1 := by field_simp
  obtain ⟨a,r,hr,hball,hshape⟩ := hballs o δ hδ N h hh hlower hupper
  have hu : WeakSobolevJet.value u ∈ M.conformingSpace
      (dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) := by
    rw [cartesianKuhnReconstructionJet_value]
    exact cartesianKuhnReconstructionLp_mem_conforming o δ hδ N f
  have hf : WeakSobolevJet.value u=M.nodalLp hS.measurableSet
      (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianInteriorData o δ N f) := by
    rw [cartesianKuhnReconstructionJet_value,cartesianKuhnReconstructionLp_eq_nodal]
  obtain ⟨e,he,hnorm⟩ := hbound M (cartesianKuhnPartition_faceMatching o δ hδ N)
    (cartesianKuhnPartition_boundaryFitted o δ hδ N) w τ t η hη hmesh
    a (fun _ => r) (fun _ => hr) hball hshape u (cartesianInteriorData o δ N f) hu hf
  have hI : M.nodalLp hS.measurableSet (cartesianKuhnPartition_faceMatching o δ hδ N)
      (fun x => (σ.mul σ).value x*cartesianInteriorData o δ N f x)=
      cartesianKuhnReconstructionLp o δ hδ N (cartesianSquaredWeightTest o δ N σ.value f) := by
    rw [cartesianKuhnReconstructionLp_eq_nodal]
    change M.nodalLp _ _ _=M.nodalLp _ _
      (cartesianInteriorData o δ N (cartesianNodalMultiplier o δ N (fun x => (σ.value x)^2) f))
    rw [cartesianInteriorData_multiplier]
    simp only [BoundedMultiplier.mul,pow_two]
  refine ⟨e,?_,?_⟩
  · change WeakSobolevJet.value e=_-(σ.mul σ).map _
    rw [he,hI,cartesianKuhnReconstructionJet_value]
    rfl
  · change WeakSobolevJet.weightedNorm (w.q t) ξ e ≤
      (C*(d+1:ℝ))*h*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u
    calc
      _ ≤ C*M.maxDiameter*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u := hnorm
      _ ≤ C*((d+1:ℝ)*h)*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u := by
        apply mul_le_mul_of_nonneg_right _ (WeakSobolevJet.weightedNorm_nonneg _ _ _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hC.le) ((w.nonneg t).trans (w.upper t))
      _ = _ := by ring

end Carleman
