-- Prove2me | Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_refined
-- name    : mme_independent_blocks_form_direct_sum_restrict_refined
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-06-01T00:29:55.969261+00:00
-- url     : https://prove2.me/theorems/ef9d25d2-8057-42af-af2b-6050fee61f34
-- statement:
--   **Pairwise mode-disjoint block subtensors form a direct-sum Restrict of T** — REFINED concrete-statement version of `mme_independent_blocks_form_direct_sum_restrict` using the new `blockSubtensor` API. Hypothesis: C ⊆ (Fin 3 → Fin t) is pairwise mode-disjoint (∀ distinct σ, σ' ∈ C, ∀ i, σ i ≠ σ' i). Conclusion: any enumeration B : Fin C.card → TensorObj K 3 of the block subtensors over C satisfies Restrict (bigAdd B) T. Replaces the original True-placeholder hypotheses with this concrete pairwise-disjointness condition. ~150-300 LOC proof via Submodule.iSupIndep applied mode-wise. Every laser-method Salem-Spencer-direct-sum step now has a concrete reusable target.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_independent_blocks_form_direct_sum_restrict_refined {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t) (C : Finset (Fin 3 → Fin t)) (_hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin 3, σ i ≠ σ' i) (B : Fin C.card → TensorObj K 3) (_hB : ∀ j : Fin C.card, ∃ σ ∈ C, B j = G.blockSubtensor σ) : TensorObj.Restrict (TensorObj.bigAdd B) T := by sorry
