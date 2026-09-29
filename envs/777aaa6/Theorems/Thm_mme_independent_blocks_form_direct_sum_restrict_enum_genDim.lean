-- Prove2me | Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_enum_genDim
-- name    : mme_independent_blocks_form_direct_sum_restrict_enum_genDim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-06-05T01:29:50.5425+00:00
-- url     : https://prove2.me/theorems/1be4ef16-9845-464c-975d-43512863908c
-- statement:
--   General mode-dimension form of the independent-blocks direct-sum restriction. For a tensor $T$ of any order $d$ with a type grading $G$ into $t$ classes, and a finite injective family $\sigma_s$ of multi-types in a set $C$ that are pairwise distinct at every mode and whose complement blocks vanish, the direct sum $\bigoplus_j G.\text{blockSubtensor}(\sigma_s j)$ restricts into $T$. Generalizes the order-3 version to arbitrary $d$ (needed for the squared/Fin 6 CW laser construction).

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_independent_blocks_form_direct_sum_restrict_enum_genDim
    {K : Type u} [Field K] {d : ℕ} {T : TensorObj K d} {t : ℕ}
    (G : T.TypeGrading t)
    (C : Finset (Fin d → Fin t))
    (σs : Fin C.card → (Fin d → Fin t))
    (hσs : ∀ j, σs j ∈ C)
    (hσs_inj : Function.Injective σs)
    (hDisj : ∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → ∀ i : Fin d, σ i ≠ σ' i)
    (hSupp : ∀ σ : Fin d → Fin t, σ ∉ C → G.blockTensor σ = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j => G.blockSubtensor (σs j))) T := by sorry
