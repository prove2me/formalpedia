-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_close_of_sqrt33
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_close_of_sqrt33
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:04.040869+00:00
-- url     : https://prove2.me/theorems/7ae3ee31-7de7-4f4c-81fa-ab0db8470b40
-- title:
--   A prime divisor above k in the close below-square subcase
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\ge9$, $2k\le n$, and $n<k^2$. Put $r=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$. Assume $r\ge33$ and
--   $$\max(M-r,0)\le r.$$
--   Then some prime p satisfies $p>k$ and $p\mid\binom nk$. The maximum expresses Lean’s truncated natural-number subtraction in the premise.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L2009. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03
set_option maxHeartbeats 800000

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_close_of_sqrt33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
