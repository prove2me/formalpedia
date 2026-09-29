-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_020
-- name    : mme_CW_block_is_MM_at_020
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:22:12.480024+00:00
-- url     : https://prove2.me/theorems/fd289b60-65bf-4d5a-a2a5-bde2a43c9c25
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (O, T, O) = (0, 2, 0)$.** The $\sigma$-block at $(0, 2, 0)$ in the canonical 3-grading on $\mathrm{CWObj}\,K\,q$ contains the single rank-one term $e_O \otimes e_T \otimes e_O$ of $T_q$. After class-isomorphism this is $\mathrm{MMObj}\,K\,1\,1\,1$.
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

/-- **CW per-s MM witness at σ = (O, T, O) = (0, 2, 0).**

The σ-block at (0, 2, 0) contains the single rank-one term
`e_O ⊗ e_T ⊗ e_O` of `T_q`. After class-isomorphism this is `MMObj K 1 1 1`. -/
theorem mme_CW_block_is_MM_at_020
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 0
        | ⟨1, _⟩ => 2
        | ⟨2, _⟩ => 0)) := by
  sorry
