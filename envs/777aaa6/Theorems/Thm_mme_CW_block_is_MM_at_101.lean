-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_101
-- name    : mme_CW_block_is_MM_at_101
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:23:14.591766+00:00
-- url     : https://prove2.me/theorems/70268f83-91af-4546-bfad-b06e6dbfa9ab
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (M, O, M) = (1, 0, 1)$.** The $\sigma$-block at $(1, 0, 1)$ extracts the rank-$q$ middle-type pattern of $T_q$: $\sum_{i=1}^q e_{M_i} \otimes e_O \otimes e_{M_i}$. After class-isomorphism this matches $\mathrm{MMObj}\,K\,q\,1\,1$.
-- source:
--   Coppersmith-Winograd 1990 §6 middle support pattern

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading

open MME

universe u

/-- **CW per-s MM witness at σ = (M, O, M) = (1, 0, 1).**

The σ-block at (1, 0, 1) extracts the rank-q middle-type pattern of `T_q`:
`∑ᵢ e_{Mᵢ} ⊗ e_O ⊗ e_{Mᵢ}`. After class-isomorphism this matches
`MMObj K q 1 1` (= `∑ᵢ e_{i,0} ⊗ e_{0,0} ⊗ e_{0,i}`). -/
theorem mme_CW_block_is_MM_at_101
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K q 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 0
        | ⟨2, _⟩ => 1)) := by
  sorry
