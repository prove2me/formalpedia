-- Prove2me | Theorems.Thm_mme_kronFin_adjacent_swap_basis_word_semantics
-- name    : mme_kronFin_adjacent_swap_basis_word_semantics
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:14:29.422647+00:00
-- url     : https://prove2.me/theorems/5a775303-d960-461a-a699-ff8d7ee652e9
-- title:
--   Recursive adjacent Kronecker swap has the ordinary dependent basis semantics
-- statement:
--   Under the recursive adjacent exchange of heterogeneous Kronecker factors at positions $j$ and $j+1$, the factor basis at each position is exactly the original basis at the transposed position. Applying the recursive word-restoration operation has the same pointwise effect. If $s_j$ denotes the adjacent transposition, both outputs at $r$ are therefore the corresponding input data at $s_j(r)$. Heterogeneous equality records the dependent change of basis-index and vector-space types. This is the exact coordinate semantics required for source-word regrouping in the asymmetric hashing construction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_adjacent_swap_data

open MME Module

universe u

set_option autoImplicit false

theorem mme_kronFin_adjacent_swap_basis_word_semantics
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    (∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i)) (r : Fin (n + 2)),
      HEq (TensorObj.kronFinAdjacentSwapBasis T j i b r)
        (b (Equiv.swap j.castSucc j.succ r))) ∧
    ∀ (index : Fin (n + 2) → Type u)
        (w : ∀ r, TensorObj.kronFinAdjacentSwapIndex index j r)
        (r : Fin (n + 2)),
      HEq (TensorObj.kronFinAdjacentUnswapWord j w r)
        (w (Equiv.swap j.castSucc j.succ r)) := by
  sorry
