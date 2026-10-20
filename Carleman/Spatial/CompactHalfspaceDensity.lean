module
public import Carleman.Spatial.StrongH2CutoffTransfer
/-! Genuine compact-support localization yields zero-boundary strong H²
approximation on both actual half-spaces, and interior full-space approximation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S T K : Set (SpatialCoordinates d)}
namespace SpatialTest

theorem cutoffH2Transfer_roundtrip (η : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hS : IsOpen S) (hT : IsOpen T) (hST : S∩tsupport η.value⊆T) (hTS : T∩tsupport η.value⊆S)
    (hregS : DirichletH2Regular S) (hregT : DirichletH2Regular T) (u : dirichletH2JetSpace S)
    (hu : (fun x => η.value x*WeakSobolevJet.value u.val x) =ᵐ[volume.restrict S] WeakSobolevJet.value u.val) :
    η.cutoffH2Transfer hT hS hTS hST hregS
      ⟨η.cutoffH2Transfer hS hT hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS hT hST hTS hregT u⟩=u.val := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  apply Lp.ext
  have hv := ((ae_restrict_iff' hT.measurableSet).mp (η.cutoffH2Transfer_ae hS hT hST hTS hregT u)).filter_mono
    (ae_restrict_le (s := S))
  filter_upwards [η.cutoffH2Transfer_ae hT hS hTS hST hregS
    ⟨η.cutoffH2Transfer hS hT hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS hT hST hTS hregT u⟩,
    hv,hu,ae_restrict_mem hS.measurableSet] with x ho hi hu hxS
  rw [ho]
  by_cases hη : η.value x=0
  · simpa only [hη,zero_mul] using hu
  · have hxT := hST ⟨hxS,subset_tsupport _ hη⟩
    rw [indicator_of_mem hxT,hi hxT,indicator_of_mem hxS,hu,hu]

end SpatialTest

theorem exists_compact_localbox_strong_h2_approximation
    (hS : IsOpen S) (hregS : DirichletH2Regular S)
    (η : SpatialTest (univ : Set (SpatialCoordinates d))) (hη : ∀ x∈K, η.value x=1)
    (a b : Fin d → ℝ) (hpos : ∀ i, a i<b i)
    (hST : S∩tsupport η.value⊆openCoordinateBox a b)
    (hTS : openCoordinateBox a b∩tsupport η.value⊆S)
    (u : dirichletH2JetSpace S)
    (hu : ∀ᵐ x ∂volume.restrict S, x∉K → WeakSobolevJet.value u.val x=0) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier S, (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2) ((U n).allOrderJetOn S 2)∈dirichletJetSpace S) ∧
      Tendsto (fun n => (U n).allOrderJetOn S 2) atTop (𝓝 u.val) := by
  have ht := openCoordinateBox_isOpen a b
  have hregT := dirichletH2Regular_box a b hpos
  let v : dirichletH2JetSpace (openCoordinateBox a b) :=
    ⟨η.cutoffH2Transfer hS ht hST hTS hregT u,η.cutoffH2Transfer_dirichlet hS ht hST hTS hregT u⟩
  have hm : (fun x => η.value x*WeakSobolevJet.value u.val x) =ᵐ[volume.restrict S] WeakSobolevJet.value u.val := by
    filter_upwards [hu] with x hx
    by_cases hk : x∈K
    · rw [hη x hk,one_mul]
    · rw [hx hk,mul_zero]
  have he : η.cutoffH2Transfer ht hS hTS hST hregS v=u.val :=
    η.cutoffH2Transfer_roundtrip hS ht hST hTS hregS hregT u hm
  obtain ⟨U,hU,hD,hlim⟩ := η.exists_cutoff_box_strong_h2_approximation a b hpos hS hTS hST hregS v
  exact ⟨U,hU,hD,he ▸ hlim⟩

def signedCoordinateHalfspace (r : Fin d) (upper : Bool) : Set (SpatialCoordinates d) :=
  if upper then {x | 0<x r} else {x | x r<0}

theorem signedCoordinateHalfspace_isOpen (r : Fin d) (upper : Bool) :
    IsOpen (signedCoordinateHalfspace r upper) := by
  cases upper
  · exact isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r) continuous_const
  · exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)

theorem dirichletH2Regular_signedHalfspace (r : Fin d) (upper : Bool) :
    DirichletH2Regular (signedCoordinateHalfspace r upper) := by
  have hS := signedCoordinateHalfspace_isOpen r upper
  intro u hu f hf
  have hinv : ∀ j : Fin d, j≠r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' signedCoordinateHalfspace r upper ⊆
        signedCoordinateHalfspace r upper := by
    intro j hj t x hx
    have he : (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r=x r := by
      simp [EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,Ne.symm hj]
    cases upper <;> simpa only [signedCoordinateHalfspace,Bool.false_eq_true,ite_false,ite_true,mem_ofPred_eq,mem_preimage,he] using hx
  obtain ⟨U,hU,_⟩ := exists_dirichlet_H2_of_tangential_invariance hS u hu f hf r hinv
  exact ⟨U,hU⟩

theorem exists_signedHalfspace_box_cutoff (r : Fin d) (upper : Bool) (hK : IsCompact K) :
    ∃ (a b : Fin d → ℝ) (η : SpatialTest (univ : Set (SpatialCoordinates d))),
      (∀ i, a i<b i) ∧ (∀ x∈K, η.value x=1) ∧
      signedCoordinateHalfspace r upper∩tsupport η.value⊆openCoordinateBox a b ∧
      openCoordinateBox a b∩tsupport η.value⊆signedCoordinateHalfspace r upper := by
  classical
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : SpatialCoordinates d)
  obtain ⟨η,hη⟩ := exists_spatialTest_eq_one_on_compact Metric.isOpen_ball hK hKR
  let a : Fin d → ℝ := fun i => if i=r ∧ upper=true then 0 else -R
  let b : Fin d → ℝ := fun i => if i=r ∧ upper=false then 0 else R
  refine ⟨a,b,η.toUniv,?_,hη,?_,?_⟩
  · intro i
    by_cases hi : i=r
    · subst i
      cases upper <;> simp [a,b,hR]
    · simp only [a,b,hi,false_and,ite_false]
      linarith
  · rintro x ⟨hx,hxη⟩
    have hn : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using η.support hxη
    intro i
    have hc0 : |x i|≤‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hc : |x i|<R := hc0.trans_lt hn
    have hci := abs_lt.mp hc
    by_cases hi : i=r
    · subst i
      cases upper
      · change x r<0 at hx
        simpa only [a,b,Bool.false_eq_true,and_false,ite_false,and_self,ite_true] using And.intro hci.1 hx
      · change 0<x r at hx
        simpa only [a,b,Bool.true_eq_false,and_false,ite_false,and_self,ite_true] using And.intro hx hci.2
    · simpa only [a,b,hi,false_and,ite_false] using hci
  · rintro x ⟨hx,_⟩
    have hr := hx r
    cases upper
    · change x r<0
      simpa only [a,b,Bool.false_eq_true,and_false,ite_false,and_self,ite_true] using hr.2
    · change 0<x r
      simpa only [a,b,Bool.true_eq_false,and_false,ite_false,and_self,ite_true] using hr.1

theorem exists_compact_halfspace_strong_h2_approximation (r : Fin d) (upper : Bool)
    (hK : IsCompact K) (u : dirichletH2JetSpace (signedCoordinateHalfspace r upper))
    (hu : ∀ᵐ x ∂volume.restrict (signedCoordinateHalfspace r upper),
      x∉K → WeakSobolevJet.value u.val x=0) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x∈frontier (signedCoordinateHalfspace r upper), (U n).value x=0) ∧
      (∀ n, WeakSobolevJet.truncate (by decide : 1≤2)
        ((U n).allOrderJetOn (signedCoordinateHalfspace r upper) 2)∈dirichletJetSpace (signedCoordinateHalfspace r upper)) ∧
      Tendsto (fun n => (U n).allOrderJetOn (signedCoordinateHalfspace r upper) 2) atTop (𝓝 u.val) := by
  obtain ⟨a,b,η,hpos,hη,hST,hTS⟩ := exists_signedHalfspace_box_cutoff r upper hK
  exact exists_compact_localbox_strong_h2_approximation (signedCoordinateHalfspace_isOpen r upper)
    (dirichletH2Regular_signedHalfspace r upper) η hη a b hpos hST hTS u hu
theorem dirichletH2Regular_univ (hd : 0<d) :
    DirichletH2Regular (univ : Set (SpatialCoordinates d)) := by
  intro u hu f hf
  obtain ⟨U,hU,_⟩ := exists_dirichlet_H2_of_tangential_invariance isOpen_univ u hu f hf ⟨0,hd⟩
    (fun _ _ _ => subset_univ _)
  exact ⟨U,hU⟩

theorem exists_fullspace_box_cutoff (hK : IsCompact K) :
    ∃ (a b : Fin d → ℝ) (η : SpatialTest (univ : Set (SpatialCoordinates d))),
      (∀ i, a i<b i) ∧ (∀ x∈K, η.value x=1) ∧ tsupport η.value⊆openCoordinateBox a b := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : SpatialCoordinates d)
  obtain ⟨η,hη⟩ := exists_spatialTest_eq_one_on_compact Metric.isOpen_ball hK hKR
  refine ⟨fun _ => -R,fun _ => R,η.toUniv,fun _ => by linarith,hη,?_⟩
  intro x hx i
  have hn : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using η.support hx
  have hc : |x i|≤‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  exact abs_lt.mp (hc.trans_lt hn)

theorem exists_compact_fullspace_strong_h2_approximation (hd : 0<d)
    (hK : IsCompact K) (u : dirichletH2JetSpace (univ : Set (SpatialCoordinates d)))
    (hu : ∀ᵐ x ∂volume.restrict (univ : Set (SpatialCoordinates d)),
      x∉K → WeakSobolevJet.value u.val x=0) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      Tendsto (fun n => (U n).allOrderJetOn univ 2) atTop (𝓝 u.val) := by
  obtain ⟨a,b,η,hpos,hη,hs⟩ := exists_fullspace_box_cutoff hK
  obtain ⟨U,_,_,ht⟩ := exists_compact_localbox_strong_h2_approximation isOpen_univ
    (dirichletH2Regular_univ hd) η hη a b hpos (fun _ hx => hs hx.2) (subset_univ _) u hu
  exact ⟨U,ht⟩

end Carleman
