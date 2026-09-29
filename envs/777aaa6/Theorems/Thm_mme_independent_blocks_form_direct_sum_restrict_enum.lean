-- Prove2me | Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_enum
-- name    : mme_independent_blocks_form_direct_sum_restrict_enum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-01T01:51:46.41151+00:00
-- url     : https://prove2.me/theorems/3ba901ad-e8ab-4ead-a75e-0088ee5734b8
-- statement:
--   Pairwise mode-disjoint, C-supported, injectively-enumerated block subtensors form a direct-sum Restrict of T - fully corrected refinement. Adds Function.Injective σs to the _aligned variant (which still allowed duplicate B's, breaking the natural witness). With σs injective: non-constant ψ implies σ_ψ ∉ C, hence hSupp kills the cross-term. Suffix _enum: B is enumeration of C-distinct blocks. The canonical use case (σs := Finset.equivFin) automatically satisfies injectivity. Discovered 2026-05-31 via subagent finding the duplicate-B failure mode in the previous aligned variant.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_independent_blocks_form_direct_sum_restrict_enum {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t) (C : Finset (Fin 3 → Fin t)) (σs : Fin C.card → (Fin 3 → Fin t)) (_hσs : ∀ j, σs j ∈ C) (_hσs_inj : Function.Injective σs) (_hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin 3, σ i ≠ σ' i) (_hSupp : ∀ σ : Fin 3 → Fin t, σ ∉ C → G.blockTensor σ = 0) : TensorObj.Restrict (TensorObj.bigAdd (fun j => G.blockSubtensor (σs j))) T := by sorry
