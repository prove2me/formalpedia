-- Prove2me | Theorems.Thm_mme_uniform_direct_sum_grading_certificate
-- name    : mme_uniform_direct_sum_grading_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:21:32.303711+00:00
-- url     : https://prove2.me/theorems/5b31a918-02c2-4aed-945d-a4c72d652d7c
-- title:
--   Canonical supported-block certificate for a uniform direct sum
-- statement:
--   Let $S,T$ be order-three tensors over a field $K$. If $T$ restricts to a direct sum of $n$ copies of $S$, there is a restriction $P$ of $T$ with a grading whose supported address set has cardinality $n$. These addresses are disjoint in every mode, all other blocks vanish, and each supported block restricts to $S$. The statement includes the empty direct sum.
-- source:
--   Canonical tensor isomorphisms and grading certificates.

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_rank_bridge
open MME
universe u
set_option autoImplicit false

theorem mme_uniform_direct_sum_grading_certificate
    {K : Type u} [Field K] (S T : TensorObj K 3) (n : ℕ)
    (h : TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin n ↦ S)) T) :
    ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      TensorObj.Restrict P T ∧
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict S (grading.blockSubtensor (σs j))) ∧
      C.card = n := by sorry
