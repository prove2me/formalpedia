-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_far_of_120_le
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_far_of_120_le
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:08.017351+00:00
-- url     : https://prove2.me/theorems/426a8de9-4895-4993-bedf-6e79bd5417c3
-- title:
--   A prime divisor above k in the far below-square subcase
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\ge120$, $2k\le n$, and $n<k^2$. Put $r=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$. Assume $r\ge33$ and $2r<M$. Then there is a prime p with
--   $$p>k,\qquad p\mid\binom nk.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L1991. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_far_of_120_le
    {n k : ℕ} (hk120 : 120 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hfar : 2 * sqrt n < min k (n / 3)) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
