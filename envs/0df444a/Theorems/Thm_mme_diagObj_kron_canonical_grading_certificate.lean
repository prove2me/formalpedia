-- Prove2me | Theorems.Thm_mme_diagObj_kron_canonical_grading_certificate
-- name    : mme_diagObj_kron_canonical_grading_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:19:33.978653+00:00
-- url     : https://prove2.me/theorems/0b2dbe94-0b54-47df-9767-f90e8aad57ba
-- title:
--   Canonical mode grading of a diagonal tensor times an arbitrary tensor
-- statement:
--   For any order-three tensor object \(S\) over a field \(K\) and any natural number \(n\), the tensor
--   \[
--   I_n\otimes S
--   \]
--   has a canonical mode grading whose retained addresses are precisely the \(n\) diagonal labels.  These labels form a set \(C\) of cardinality \(n\), have an injective enumeration, and any two distinct labels differ in every tensor mode.  Every block outside \(C\) vanishes, while every retained block restricts to \(S\).
--
--   The statement includes the case \(n=0\).  It constructs the grading and its support certificate explicitly from the diagonal tensor, rather than assuming a pre-existing direct-sum decomposition.  This is a reusable interface between concrete diagonal tensors and independent-block arguments.
-- source:
--   Elementary tensor-grading property of the diagonal tensor object and the Kronecker product.

import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_block_subtensor
open MME BigOperators
universe u

theorem mme_diagObj_kron_canonical_grading_certificate
    {K : Type u} [Field K] (S : TensorObj K 3) (n : ℕ) :
    ∃ (t : ℕ)
        (grading :
          (TensorObj.kron (TensorObj.diagObj K 3 n) S).TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict S
        (grading.blockSubtensor (σs j))) ∧
      C.card = n := by sorry
