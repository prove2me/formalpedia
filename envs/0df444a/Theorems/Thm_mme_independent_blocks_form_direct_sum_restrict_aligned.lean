-- Prove2me | Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_aligned
-- name    : mme_independent_blocks_form_direct_sum_restrict_aligned
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-06-01T01:39:38.713996+00:00
-- url     : https://prove2.me/theorems/a663dae0-83c3-4768-b062-ff192a8ee3e6
-- statement:
--   Pairwise mode-disjoint AND C-supported block subtensors form a direct-sum Restrict of T - corrected concrete-statement refinement. Strengthens the previous _refined version (which was found FALSE in |C| >= 2 case: PiTensorProduct cross-terms from mixed multi-types don't vanish without the support hypothesis hSupp: forall sigma not in C, G.blockTensor sigma = 0 - i.e. T.t is concentrated on C-typed blocks. The cross-term cancellation analysis: natural witness f i = blockProj at sigma_j i expanded via map_update_add produces k^3 terms; k diagonal sum to bigAdd, k^3-k cross-terms equal blockTensor of mixed types. hSupp makes mixed types vanish. In laser method, hSupp follows from Salem-Spencer + cyclic support pattern. Discovered 2026-05-31 via explicit Q-counterexample. Suffix _aligned per meaningful-suffix principle (support-aligned).
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_independent_blocks_form_direct_sum_restrict_aligned {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t) (C : Finset (Fin 3 → Fin t)) (_hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin 3, σ i ≠ σ' i) (_hSupp : ∀ σ : Fin 3 → Fin t, σ ∉ C → G.blockTensor σ = 0) (B : Fin C.card → TensorObj K 3) (_hB : ∀ j : Fin C.card, ∃ σ ∈ C, B j = G.blockSubtensor σ) : TensorObj.Restrict (TensorObj.bigAdd B) T := by sorry
