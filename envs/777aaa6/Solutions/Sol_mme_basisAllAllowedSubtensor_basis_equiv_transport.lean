-- Prove2me | solution 1 for mme_basisAllAllowedSubtensor_basis_equiv_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:07:23.009438+00:00
-- url     : https://prove2.me/submissions/da6f9235-d277-468b-9042-81704ba96e97

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Algebra.Module.Submodule.Equiv

open MME Module PiTensorProduct

universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZProjectionTransport

theorem class_eq_span
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) :
    (T.basisAllAllowedGrading b P).classOf i 0 =
      Submodule.span K (b i '' {x | P i x}) := by
  classical
  simp [TensorObj.basisAllAllowedGrading, TensorObj.TypeGrading.classOf,
    cwBasisGrade]

theorem proj_basis_yes
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (x : I i) (hx : P i x) :
    ((T.basisAllAllowedGrading b P).blockProj i 0 (b i x) : T.V i) = b i x := by
  classical
  have hm : b i x ∈ (T.basisAllAllowedGrading b P).classOf i 0 := by
    rw [class_eq_span]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm]

theorem proj_basis_no
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (x : I i) (hx : ¬ P i x) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ 1 (by decide)
  apply Submodule.subset_span
  exact ⟨x, by simp [hx], rfl⟩

/-- Transport a simultaneous coordinate projection through an actual
basis-aware tensor equivalence. The conclusion retains both the tensor
identity and the inclusion/projection identities, so fine-block masks can
be transported without a dimension-only isomorphism. -/
theorem _root_.solution
    {K : Type u} [Field K] (T U : TensorObj K 3)
    {I J : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (c : ∀ i, Basis (J i) K (U.V i))
    (e : ∀ i, T.V i ≃ₗ[K] U.V i) (p : ∀ i, I i ≃ J i)
    (hb : ∀ i a, e i (b i a) = c i (p i a))
    (ht : PiTensorProduct.map (fun i ↦ (e i).toLinearMap) T.t = U.t)
    (P : ∀ i, I i → Prop) (Q : ∀ i, J i → Prop)
    (hPQ : ∀ i a, P i a ↔ Q i (p i a)) :
    ∃ f : ∀ i, (T.basisAllAllowedGrading b P).classOf i 0 ≃ₗ[K]
        (U.basisAllAllowedGrading c Q).classOf i 0,
      PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
        (T.basisAllAllowedSubtensor b P).t =
          (U.basisAllAllowedSubtensor c Q).t ∧
      (∀ i a, f i ((T.basisAllAllowedGrading b P).blockProj i 0 (b i a)) =
        (U.basisAllAllowedGrading c Q).blockProj i 0 (c i (p i a))) ∧
      (∀ i x, (f i x : U.V i) = e i (x : T.V i)) := by
  classical
  let GP := T.basisAllAllowedGrading b P
  let GQ := U.basisAllAllowedGrading c Q
  have hclasses (i : Fin 3) :
      (GP.classOf i 0).map (e i).toLinearMap = GQ.classOf i 0 := by
    rw [class_eq_span, class_eq_span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨p i a, (hPQ i a).mp ha, (hb i a).symm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨b i ((p i).symm a), ⟨(p i).symm a, ?_, rfl⟩, ?_⟩
      · exact (hPQ i _).mpr (by simpa using ha)
      · simpa using hb i ((p i).symm a)
  let f (i : Fin 3) : (GP.classOf i 0) ≃ₗ[K] (GQ.classOf i 0) :=
    (e i).ofSubmodules (GP.classOf i 0) (GQ.classOf i 0) (hclasses i)
  have hinc (i : Fin 3) (x : GP.classOf i 0) :
      (f i x : U.V i) = e i (x : T.V i) := by
    exact LinearEquiv.ofSubmodules_apply (e i) (hclasses i) x
  have hproj (i : Fin 3) :
      (f i).toLinearMap.comp (GP.blockProj i 0) =
        (GQ.blockProj i 0).comp (e i).toLinearMap := by
    apply (b i).ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    by_cases ha : P i a
    · apply Subtype.ext
      rw [hinc, proj_basis_yes T b P i a ha, hb,
        proj_basis_yes U c Q i (p i a) ((hPQ i a).mp ha)]
    · rw [proj_basis_no T b P i a ha, map_zero, hb,
        proj_basis_no U c Q i (p i a) (fun h ↦ ha ((hPQ i a).mpr h))]
  refine ⟨f, ?_, ?_, hinc⟩
  · change PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
      (PiTensorProduct.map (fun i ↦ GP.blockProj i 0) T.t) =
        PiTensorProduct.map (fun i ↦ GQ.blockProj i 0) U.t
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp_rw [hproj]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, ht]
  · intro i a
    have h := LinearMap.congr_fun (hproj i) (b i a)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb] using h

end MME.DWZProjectionTransport


