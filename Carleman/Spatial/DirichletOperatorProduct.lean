module

public import Carleman.Spatial.WeakLaplacianProduct
public import Carleman.Weights.DirichletAllowedWeight

/-! A bounded smooth coefficient preserves the genuine form-operator
Dirichlet domain, using its exact distributional graph characterization. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def smoothLaplacianCorrection (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) : Lp ℝ 2 (volume.restrict S) :=
  ∑ i : Fin d,
    ((2:ℝ) • (intrinsicWordMultiplier hS (ae_restrict_mem hS.measurableSet) hw [i]).map
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
      (intrinsicWordMultiplier hS (ae_restrict_mem hS.measurableSet) hw [i,i]).map (WeakSobolevJet.value u))

theorem boundedSmooth_weakLaplacian_product (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ p : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value p=w.map (WeakSobolevJet.value u) ∧ p ∈ dirichletJetSpace S ∧
      IsWeakNegativeLaplacian p (w.map f-smoothLaplacianCorrection hS w hw u) := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let dw := fun i => intrinsicWordMultiplier hS hν hw [i]
  let ddw := fun i => intrinsicWordMultiplier hS hν hw [i,i]
  have hdw (i : Fin d) : (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    change wordDerivative [i] w.value =ᵐ[volume.restrict S] _
    simpa only [intrinsicWordMultiplier,wordDerivative_nil] using
      intrinsicWordMultiplier_derivative hS hν hw [] i
  have hddw (i : Fin d) : (ddw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ (dw i).value x (EuclideanSpace.basisFun (Fin d) ℝ i)) :=
    intrinsicWordMultiplier_derivative hS hν hw [i] i
  refine ⟨weakFirstProduct hS hν w dw hw.1 hdw u,weakFirstProduct_value hS hν w dw hw.1 hdw u,
    weakFirstProductCLM_mem_dirichlet hS w dw hw.1 hdw u hu,?_⟩
  exact hf.mul hS w dw ddw hw.1 (fun i => intrinsicWordMultiplier_smooth hS hν hw [i]) hdw hddw u f

theorem boundedSmooth_dirichlet_operator_product (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (w : BoundedMultiplier (volume.restrict S))
    (hw : BoundedSmoothOn w.value S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    ∃ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      (z : Lp ℝ 2 (volume.restrict S))=w.map (WeakSobolevJet.value u) ∧
      (boundedDirichletOriginalForm hS hd hb).model.operator z=
        w.map f-smoothLaplacianCorrection hS w hw u := by
  obtain ⟨p,hp,hpdir,hpg⟩ := boundedSmooth_weakLaplacian_product hS w hw u hu f hf
  exact (dirichlet_operator_graph_iff hS hd hb _ _).mpr ⟨p,hp,hpdir,hpg⟩

theorem boundedSmooth_map_mem_dirichlet_domain (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (w : BoundedMultiplier (volume.restrict S))
    (hw : BoundedSmoothOn w.value S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    w.map (z : Lp ℝ 2 (volume.restrict S)) ∈ (boundedDirichletOriginalForm hS hd hb).model.domain := by
  obtain ⟨u,huz,hu,hf⟩ := (dirichlet_operator_graph_iff hS hd hb (z : Lp ℝ 2 (volume.restrict S))
    ((boundedDirichletOriginalForm hS hd hb).model.operator z)).mp ⟨z,rfl,rfl⟩
  obtain ⟨p,hp,hpdir,hpg⟩ := boundedSmooth_weakLaplacian_product hS w hw u hu _ hf
  obtain ⟨v,hv,_⟩ := (dirichlet_operator_graph_iff hS hd hb _ _).mpr ⟨p,hp,hpdir,hpg⟩
  rw [huz] at hv
  rw [← hv]
  exact v.property

theorem allowed_weight_mem_dirichlet_domain (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (hρ : SmoothOnClosure ρ.value S) (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    ((ρ.scaled η).multiplier w τ t).map (z : Lp ℝ 2 (volume.restrict S)) ∈
      (boundedDirichletOriginalForm hS hd hb).model.domain :=
  boundedSmooth_map_mem_dirichlet_domain hS hd hb _
    (allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη) z

end Carleman
