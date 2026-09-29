-- Prove2me | solution 1 for mme_modern_grouped_fine_y_then_z_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T03:59:08.885778+00:00
-- url     : https://prove2.me/submissions/c14f4a49-1898-490b-9722-05b00035f949

import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem rejected_basis_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop)
    (i : Fin 3) (x : ι i) (hx : ¬ allowed i x) :
    (T.basisAllAllowedGrading b allowed).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne
    (T.basisAllAllowedGrading b allowed) i 0 1 (by decide)
  change b i x ∈ cwBasisGrade (b i)
    (fun j ↦ if allowed i j then (0 : Fin 2) else 1) 1
  apply Submodule.subset_span
  exact ⟨x, by simp [hx], rfl⟩

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {ι : Fin 3 → Type u} [∀ i, Fintype (ι i)]
    {Label : Fin 3 → Type v}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (fineLabel : (i : Fin 3) → ι i → Label i)
    (allowed : Fin k → (i : Fin 3) → Label i → Prop)
    (compatibleY : Label 1 → Fin k → Prop)
    (compatibleZ : Label 2 → Fin k → Prop)
    (hYUnique : ∀ (j j' : Fin k) (y : Label 1),
      allowed j 1 y → compatibleY y j' → j' = j)
    (hSupportedY : ∀ (x : (i : Fin 3) → ι i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, allowed (js i) i (fineLabel i (x i))) →
      compatibleY (fineLabel 1 (x 1)) (js 0))
    (hZUnique : ∀ (j j' : Fin k) (z : Label 2),
      allowed j 2 z → compatibleZ z j' → j' = j)
    (hSupportedZ : ∀ (x : (i : Fin 3) → ι i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, allowed (js i) i (fineLabel i (x i))) →
      js 0 = js 1 →
      compatibleZ (fineLabel 2 (x 2)) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        T.basisAllAllowedSubtensor b
          (fun i x ↦ allowed j i (fineLabel i x))))
      T := by
  classical
  let keep : Fin k → (i : Fin 3) → ι i → Prop :=
    fun j i x ↦ allowed j i (fineLabel i x)
  let B : Fin k → TensorObj K 3 :=
    fun j ↦ T.basisAllAllowedSubtensor b (keep j)
  let f : ∀ j : Fin k, ∀ i : Fin 3, T.V i →ₗ[K] (B j).V i :=
    fun j i ↦ (T.basisAllAllowedGrading b (keep j)).blockProj i 0
  apply mme_tensor_family_direct_sum_restrict_of_mixed_maps T B f
  · intro j
    rfl
  · intro js hNonconstant
    rw [← (Basis.piTensorProduct b).sum_repr T.t, map_sum]
    apply Finset.sum_eq_zero
    intro x _
    rw [map_smul]
    by_cases hcoeff : (Basis.piTensorProduct b).repr T.t x = 0
    · rw [hcoeff, zero_smul]
    · have hRejected : ∃ i : Fin 3, ¬ keep (js i) i (x i) := by
        by_contra h
        have hKeep : ∀ i, allowed (js i) i (fineLabel i (x i)) := by
          intro i
          by_contra hi
          exact h ⟨i, hi⟩
        have hXY : js 0 = js 1 :=
          hYUnique (js 1) (js 0) (fineLabel 1 (x 1))
            (hKeep 1) (hSupportedY x js hcoeff hKeep)
        have hXZ : js 0 = js 2 :=
          hZUnique (js 2) (js 0) (fineLabel 2 (x 2))
            (hKeep 2) (hSupportedZ x js hcoeff hKeep hXY)
        apply hNonconstant (js 0)
        funext i
        fin_cases i
        · rfl
        · exact hXY.symm
        · exact hXZ.symm
      obtain ⟨i, hi⟩ := hRejected
      have hzero : f (js i) i (b i (x i)) = 0 :=
        rejected_basis_projection_zero T b (keep (js i)) i (x i) hi
      rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        (PiTensorProduct.tprod K).map_coord_zero i hzero, smul_zero]
