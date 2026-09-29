-- Prove2me | solution 1 for mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:19:52.188704+00:00
-- url     : https://prove2.me/submissions/96054887-f5ac-46f2-934f-25a09e69bfd1

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZStandardForm

theorem allowed_basis_mem
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P : (i : Fin 3) → ι i → Prop) (i : Fin 3) (x : ι i) (hx : P i x) :
    b i x ∈ (T.basisAllAllowedGrading b P).classOf i 0 := by
  classical
  apply Submodule.subset_span
  exact ⟨x, by simp [hx], rfl⟩

theorem disallowed_basis_mem
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P : (i : Fin 3) → ι i → Prop) (i : Fin 3) (x : ι i) (hx : ¬ P i x) :
    b i x ∈ (T.basisAllAllowedGrading b P).classOf i 1 := by
  classical
  apply Submodule.subset_span
  exact ⟨x, by simp [hx], rfl⟩

theorem allowed_projection_basis_of_mem
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P : (i : Fin 3) → ι i → Prop) (i : Fin 3) (x : ι i) (hx : P i x) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i x) =
      ⟨b i x, allowed_basis_mem T b P i x hx⟩ := by
  exact TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ _

theorem allowed_projection_basis_of_not_mem
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P : (i : Fin 3) → ι i → Prop) (i : Fin 3) (x : ι i) (hx : ¬ P i x) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i x) = 0 := by
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ 1 (by decide) _
    (disallowed_basis_mem T b P i x hx)


end MME.DWZStandardForm

open MME.DWZStandardForm

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} [∀ i, Fintype (ι i)]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (P Q : (i : Fin 3) → ι i → Prop)
    (hsupport : ∀ x : (i : Fin 3) → ι i,
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, Q i (x i)) → ∀ i, P i (x i)) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b Q)
      (T.basisAllAllowedSubtensor b P) := by
  classical
  let GP := T.basisAllAllowedGrading b P
  let GQ := T.basisAllAllowedGrading b Q
  let f (i : Fin 3) : (GP.classOf i 0) →ₗ[K] (GQ.classOf i 0) :=
    (GQ.blockProj i 0).comp (GP.classOf i 0).subtype
  refine ⟨f, ?_⟩
  change PiTensorProduct.map f (PiTensorProduct.map (fun i ↦ GP.blockProj i 0) T.t) =
    PiTensorProduct.map (fun i ↦ GQ.blockProj i 0) T.t
  conv_lhs => rw [← (Basis.piTensorProduct b).sum_repr T.t]
  conv_rhs => rw [← (Basis.piTensorProduct b).sum_repr T.t]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : (Basis.piTensorProduct b).repr T.t x = 0
  · simp only [hc, zero_smul]
  · congr 1
    rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    by_cases hp : ∀ i, P i (x i)
    · congr 1
      funext i
      change GQ.blockProj i 0 ((GP.blockProj i 0 (b i (x i)) : GP.classOf i 0) : T.V i) = _
      rw [allowed_projection_basis_of_mem T b P i (x i) (hp i)]
    · obtain ⟨i, hi⟩ := not_forall.mp hp
      have hq : ¬ ∀ i, Q i (x i) := fun hq ↦ hp (hsupport x hc hq)
      obtain ⟨j, hj⟩ := not_forall.mp hq
      have hleft : PiTensorProduct.tprod K
          (fun i ↦ f i (GP.blockProj i 0 (b i (x i)))) = 0 := by
        apply (PiTensorProduct.tprod K).map_coord_zero i
        rw [allowed_projection_basis_of_not_mem T b P i (x i) hi]
        exact map_zero _
      have hright : PiTensorProduct.tprod K
          (fun i ↦ GQ.blockProj i 0 (b i (x i))) = 0 := by
        apply (PiTensorProduct.tprod K).map_coord_zero j
        exact allowed_projection_basis_of_not_mem T b Q j (x j) hj
      exact hleft.trans hright.symm
