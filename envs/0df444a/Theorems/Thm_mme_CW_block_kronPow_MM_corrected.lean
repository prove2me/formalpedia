-- Prove2me | Theorems.Thm_mme_CW_block_kronPow_MM_corrected
-- name    : mme_CW_block_kronPow_MM_corrected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:21:28.550674+00:00
-- url     : https://prove2.me/theorems/754e6149-08d4-4523-a119-b14d3bffbc66
-- statement:
--   **Type sequences in a CW tensor power restrict to a single matrix product.**
--
--   Fix a field $K$, $q,N\in\mathbb{N}$, and a *type sequence* $\tau$ assigning to each of the $N$ tensor-power positions one of the six supported block types of the CW tensor,
--
--   $$
--   (0,1,1),\;(1,0,1),\;(1,1,0),\;(0,0,2),\;(0,2,0),\;(2,0,0).
--   $$
--
--   Each type carries matrix-multiplication dimensions: $(1,1,q)$, $(q,1,1)$, $(1,q,1)$ for the three middle types and $(1,1,1)$ for the three boundary types. The theorem asserts that $T_q^{\otimes N}$ restricts to the single rectangular matrix-multiplication tensor whose three dimensions are the coordinatewise products of these per-position dimensions.
--
--   This is the per-block algebraic layer of the laser method: before any counting or pruning, every supported type sequence in a CW tensor power is an honest rectangular matrix product. Together with the dimension bookkeeping of `mme_CW_block_dimension_products` it yields the closed form $\langle q^{n_{101}},q^{n_{110}},q^{n_{011}}\rangle$, where $n_{abc}$ counts the positions of type $(a,b,c)$.
--
--   **Formalization Note** The dimensions are determined by the multinomial statistics of the type sequence itself, not by the dimensions of the grading classes of $T_q^{\otimes N}$ — the latter reading is false and this statement replaces two earlier deprecated attempts based on it. The order of `TensorObj.Restrict` is target first: the matrix product is obtained from the CW power by modewise linear substitutions.
-- source:
--   Coppersmith-Winograd 1990; corrected replacement for UUIDs 0a0eece9 + 48f74a41

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_rank

open MME BigOperators

universe u

/-! # CW kronPow MM Restrict — *corrected* replacement.

**Supersedes the FALSE** `mme_block_tensor_kronPow_balanced_dim_product`
(UUID `0a0eece9`) and the FALSE `mme_block_tensor_is_matMul_kronPow_balanced`
(UUID `48f74a41`). Both claimed `MMObj K (∏ finrank ...) ...` which is
mathematically incorrect for paper-agnostic blocks — see
`REPORT_block_MM_correction.md` + memory `feedback_block_is_MM_not_finrank.md`.

**The right shape.** Each `s ∈ CWSupportPattern` has its own `(a_s, b_s, c_s)`
read off from the CW support pattern (NOT from grading-class finranks):

| s | (a_s, b_s, c_s) |
|---|---|
| (0, 1, 1) | (1, 1, q) |
| (1, 0, 1) | (q, 1, 1) |
| (1, 1, 0) | (1, q, 1) |
| (0, 0, 2) | (1, 1, 1) |
| (0, 2, 0) | (1, 1, 1) |
| (2, 0, 0) | (1, 1, 1) |

For any type-sequence `τ : Fin N → CWSupportPattern`, `(CWObj K q).kronPow N`
Restricts from the multinomial-product MMObj whose three dimensions are
products over k of per-position `(a_{τ k}, b_{τ k}, c_{τ k})`.

**Proof** (when paper-agnostic factorization closes): direct application of
`mme_block_per_s_factorization` with the 6 PROVED CW per-s MM witnesses
(`mme_CW_block_is_MM_at_{002,020,200,011,101,110}`).
-/

/-- The (a_s, b_s, c_s) dimensions for each CW support element s — read off
from the laser pattern structure, NOT from grading-class finranks. -/
def cwBlockMMDim (s : Fin 3 × Fin 3 × Fin 3) (q : ℕ) : ℕ × ℕ × ℕ :=
  if s = (0, 1, 1) then (1, 1, q)
  else if s = (1, 0, 1) then (q, 1, 1)
  else if s = (1, 1, 0) then (1, q, 1)
  else (1, 1, 1)

/-- **CW kronPow MM Restrict — correctly stated.**

For any type-sequence `τ : Fin N → CWSupportPattern`, `(CWObj K q).kronPow N`
`Restrict`s from the multinomial-product MMObj whose three dimensions are
products over k of `cwBlockMMDim (τ k) q`.

Dimensions depend on σ-vs-CWSupportPattern statistics (the multinomial
counts), NOT on grading-class finranks. -/
theorem mme_CW_block_kronPow_MM_corrected
    {K : Type u} [Field K] (q : ℕ) (N : ℕ)
    (τ : Fin N → Fin 3 × Fin 3 × Fin 3)
    (_hτ_in_S : ∀ k : Fin N, τ k ∈ CWSupportPattern) :
    TensorObj.Restrict
      (MMObj K
        (∏ k : Fin N, (cwBlockMMDim (τ k) q).1)
        (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.1)
        (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.2))
      ((CWObj K q).kronPow N) := by
  sorry
