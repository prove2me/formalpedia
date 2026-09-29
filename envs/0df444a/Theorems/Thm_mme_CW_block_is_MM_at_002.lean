-- Prove2me | Theorems.Thm_mme_CW_block_is_MM_at_002
-- name    : mme_CW_block_is_MM_at_002
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:21:50.18382+00:00
-- url     : https://prove2.me/theorems/5b01c9cf-db61-430b-8e54-d6d571747556
-- statement:
--   **CW per-$s$ MM witness at $\sigma = (O, O, T) = (0, 0, 2)$.** For the canonical 3-grading on $\mathrm{CWObj}\,K\,q$ (class $0$ = $\{e_0\}$, class $1$ = middle $\{e_1, \dots, e_q\}$, class $2$ = $\{e_{q+1}\}$), the $\sigma$-block at $(0, 0, 2)$ contains exactly the single rank-one term $e_O \otimes e_O \otimes e_T$ of $T_q$. After class-isomorphism this is $\mathrm{MMObj}\,K\,1\,1\,1$ (the multiplicative unit of the tensor category).
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

/-- **CW per-s MM witness at σ = (O, O, T) = (0, 0, 2).**

The simplest of the 6 CW per-s witnesses (see `REPORT_block_MM_correction.md`,
table-3 row "(0,0,2) → MMObj K 1 1 1").

For the canonical 3-grading on `CWObj K q` (class 0 = `{e_0}`, class 1 = middle
`{e_1, …, e_q}`, class 2 = `{e_{q+1}}`, all from `Def_mme_CW_canonical_grading`),
the σ-block at `σ = (0, 0, 2)` extracts exactly one rank-one term of T_q:
`e_O ⊗ e_O ⊗ e_T`. After basis identification (each 1-dim class ↔ K), this is
`1 ⊗ 1 ⊗ 1`, which is `MMObj K 1 1 1`. -/
theorem mme_CW_block_is_MM_at_002
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => 0
        | ⟨1, _⟩ => 0
        | ⟨2, _⟩ => 2)) := by
  sorry
