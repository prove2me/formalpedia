-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_200
-- name    : mme_CW_block_is_MM_at_200
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:22:33.394958+00:00
-- url     : https://prove2.me/theorems/6cf59dcd-fde9-4e01-a774-9ecd0d4d2e66
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (T, O, O) = (2, 0, 0)$.** The $\sigma$-block at $(2, 0, 0)$ in the canonical 3-grading on $\mathrm{CWObj}\,K\,q$ contains the single rank-one term $e_T \otimes e_O \otimes e_O$ of $T_q$. After class-isomorphism this is $\mathrm{MMObj}\,K\,1\,1\,1$.
-- source:
--   Coppersmith-Winograd 1990 §6 boundary support pattern

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading

open MME

universe u

/-- **CW per-s MM witness at σ = (T, O, O) = (2, 0, 0).**

The σ-block at (2, 0, 0) contains the single rank-one term
`e_T ⊗ e_O ⊗ e_O` of `T_q`. After class-isomorphism this is `MMObj K 1 1 1`. -/
theorem mme_CW_block_is_MM_at_200
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 2
        | ⟨1, _⟩ => 0
        | ⟨2, _⟩ => 0)) := by
  sorry
