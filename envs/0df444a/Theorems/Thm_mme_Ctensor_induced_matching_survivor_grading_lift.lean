-- Prove2me | Theorems.Thm_mme_Ctensor_induced_matching_survivor_grading_lift
-- name    : mme_Ctensor_induced_matching_survivor_grading_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:14:34.950845+00:00
-- url     : https://prove2.me/theorems/dad25c72-925d-400a-a691-b9361bfcfa01
-- title:
--   Lift a C-tensor induced matching to a mode-disjoint survivor grading
-- statement:
--   Let \(T\) restrict to a direct sum of \(A^3\) macro blocks
--   \[
--   \langle H,H,H\rangle\otimes S_{L,G},
--   \]
--   and suppose independently that \(\langle H,H,H\rangle\) restricts to a direct sum of \(k\) scalar multiplications.  Then \(T\) has a further coordinate restriction equipped with a genuine mode grading whose nonzero addresses form a mode-disjoint set \(C\) of exact cardinality
--   \[
--   |C|=A^3k.
--   \]
--   Every retained graded block restricts to \(S_{L,G}\), every address outside \(C\) has zero block tensor, and the enumeration of \(C\) is injective.
--
--   This theorem is the tensor-algebra bookkeeping between the two combinatorial stages.  It must construct the summand grading and its vanishing off-diagonal blocks; it does not assume that a direct-sum grading already exists, and its restriction directions run from the macro source through the induced matching to the survivor copies.
-- source:
--   Tensor-algebra formalization of the C-tensor bookkeeping in the coupled-constituent proof of D. Coppersmith and S. Winograd (1990), journal pp. 270--272; the statement itself is a reusable restriction-and-grading lemma.

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
open MME BigOperators
universe u

theorem mme_Ctensor_induced_matching_survivor_grading_lift
    {K : Type u} [Field K]
    (T : TensorObj K 3) (L G A H k : ℕ)
    (hmacro :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
          TensorObj.kron (MMObj K H H H)
            (coupledQ6Survivor K L G)))
        T)
    (hmatching :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1))
        (MMObj K H H H)) :
    ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      TensorObj.Restrict P T ∧
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict
        (coupledQ6Survivor K L G)
        (grading.blockSubtensor (σs j))) ∧
      C.card = (A ^ 3) * k := by sorry
