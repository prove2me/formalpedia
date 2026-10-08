-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_choose_factorization_le_min_third_of_noLargePrimeFactor
-- name    : ProofsInTheBook.Chapter03.choose_factorization_le_min_third_of_noLargePrimeFactor
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:09.132687+00:00
-- url     : https://prove2.me/theorems/b258189e-43fd-4972-8426-bffd02c5357f
-- title:
--   Restricted prime factorization of a binomial coefficient
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\le n$, $2k\le n$, and $n\ge6$. Assume that every prime divisor of $B=\binom nk$ is at most k. Set $M=\min(k,\lfloor n/3\rfloor)$. Then
--   $$B=\prod_{p=0}^{M}p^{e_p},$$
--   where $e_p$ is the exponent assigned to p by the natural-number prime factorization of B, and is zero for nonprime p. Thus the displayed product is over all integers p from 0 through M, with $0^0=1$.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L208. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.choose_factorization_le_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k =
      ∏ p ∈ Finset.range (min k (n / 3) + 1),
        p ^ (n.choose k).factorization p := by sorry
