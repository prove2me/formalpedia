-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_011
-- name    : mme_CW_block_is_MM_at_011
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:22:53.602091+00:00
-- url     : https://prove2.me/theorems/aea91060-4b48-48b7-8b32-05c5d9a0e1e6
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (O, M, M) = (0, 1, 1)$.** The $\sigma$-block at $(0, 1, 1)$ extracts the rank-$q$ middle-type pattern of $T_q$: $\sum_{i=1}^q e_O \otimes e_{M_i} \otimes e_{M_i}$. After class-isomorphism (class $1 \leftrightarrow \mathrm{Fin}\,q \to K$, class $0 \leftrightarrow K$), this matches $\mathrm{MMObj}\,K\,1\,1\,q$.
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

/-- **CW per-s MM witness at σ = (O, M, M) = (0, 1, 1).**

The σ-block at (0, 1, 1) extracts the rank-q middle-type pattern of `T_q`:
`∑ᵢ e_O ⊗ e_{Mᵢ} ⊗ e_{Mᵢ}`. After class-isomorphism (class 1 ↔ `Fin q → K`,
class 0 ↔ K), this matches `MMObj K 1 1 q` (= `∑ₖ e_{00} ⊗ e_{0k} ⊗ e_{k0}`). -/
theorem mme_CW_block_is_MM_at_011
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 0
        | ⟨1, _⟩ => 1
        | ⟨2, _⟩ => 1)) := by
  sorry
