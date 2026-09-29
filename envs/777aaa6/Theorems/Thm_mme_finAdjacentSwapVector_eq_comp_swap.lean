-- Prove2me | Theorems.Thm_mme_finAdjacentSwapVector_eq_comp_swap
-- name    : mme_finAdjacentSwapVector_eq_comp_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:08:22.30993+00:00
-- url     : https://prove2.me/theorems/b35de23a-2f05-47ef-b96e-125b5bacc4ef
-- title:
--   Recursive adjacent finite-vector swap is ordinary reindexing
-- statement:
--   For a dependent finite sequence indexed by $\operatorname{Fin}(n+2)$, the recursive operation that exchanges positions $j$ and $j+1$ agrees exactly with precomposition by the ordinary adjacent transposition. In symbols, if $s_j$ swaps those two positions, then\n\n$$\operatorname{adjSwap}(T,j)(r)=T(s_j(r)).$$\n\nThis identity connects the recursion aligned with a right-associated Kronecker product to standard permutation notation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_adjacent_swap_data

open MME Module

universe u

set_option autoImplicit false

theorem mme_finAdjacentSwapVector_eq_comp_swap
    {α : Sort u} {n : ℕ} (T : Fin (n + 2) → α) (j : Fin (n + 1)) :
    TensorObj.finAdjacentSwapVector T j =
      fun r ↦ T (Equiv.swap j.castSucc j.succ r) := by
  sorry
