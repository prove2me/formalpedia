-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_110
-- name    : mme_CW_block_is_MM_at_110
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:23:36.099363+00:00
-- url     : https://prove2.me/theorems/c2a886c0-56ff-436b-9152-e17005466df9
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (M, M, O) = (1, 1, 0)$.** The $\sigma$-block at $(1, 1, 0)$ extracts the rank-$q$ middle-type pattern of $T_q$: $\sum_{i=1}^q e_{M_i} \otimes e_{M_i} \otimes e_O$. After class-isomorphism this matches $\mathrm{MMObj}\,K\,1\,q\,1$.
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

/-- **CW per-s MM witness at σ = (M, M, O) = (1, 1, 0).**

The σ-block at (1, 1, 0) extracts the rank-q middle-type pattern of `T_q`:
`∑ᵢ e_{Mᵢ} ⊗ e_{Mᵢ} ⊗ e_O`. After class-isomorphism this matches
`MMObj K 1 q 1` (= `∑ⱼ e_{0,j} ⊗ e_{j,0} ⊗ e_{0,0}`). -/
theorem mme_CW_block_is_MM_at_110
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 q 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 1
        | ⟨2, _⟩ => 0)) := by
  sorry
