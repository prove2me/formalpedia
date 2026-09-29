-- Prove2me | Theorems.Thm_mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
-- name    : mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:57:44.634264+00:00
-- url     : https://prove2.me/theorems/ad3f1ea6-c9f5-4edd-b88f-5ecf1e0f7656
-- title:
--   A common balanced coordinate half yields the paired halving structure
-- statement:
--   Let a primary hash family have coupled length $N=2n$. Suppose there is one set $S$ containing exactly half of the $2N$ tensor-power positions such that, for every retained family entry, its mode-$X$ word has exactly $n$ zeros and $n$ ones on $S$, while its mode-$Y$ word has exactly $n$ zeros and $n$ ones on the complementary half. Then the family admits a `CommonBalancedXYHalving`.
--
--   The theorem is the packaging step after double counting: once one common coordinate half has been selected, it constructs the single family-wide position equivalence required by the paired 121/211 source restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_common_paired_halving

open MME

set_option autoImplicit false

theorem mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
    {n L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H)
    (S : Finset (Fin (2 * (2 * n))))
    (hS : S.card = 2 * n)
    (hfirst : ∀ (p : Fin A × Fin H) (grade : Fin 3),
      (S.filter (fun j ↦ (family.entry p).1 0 j = grade)).card =
        if grade = 0 then n else if grade = 1 then n else 0)
    (hsecond : ∀ (p : Fin A × Fin H) (grade : Fin 3),
      ((Finset.univ \ S).filter
        (fun j ↦ (family.entry p).1 1 j = grade)).card =
        if grade = 0 then n else if grade = 1 then n else 0) :
    Nonempty family.CommonBalancedXYHalving := by
  sorry
