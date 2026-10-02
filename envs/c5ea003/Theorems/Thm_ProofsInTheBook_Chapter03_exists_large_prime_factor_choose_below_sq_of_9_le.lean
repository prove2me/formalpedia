-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_of_9_le
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_of_9_le
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:03.923718+00:00
-- url     : https://prove2.me/theorems/8df511eb-211e-4ae4-9f73-67c5f9370bfb
-- title:
--   A prime divisor above k when 2k is at most n below k squared
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\ge9$ and $2k\le n<k^2$. Then there is a prime p with
--   $$p>k,\qquad p\mid\binom nk.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3894. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n) (hnsq : n < k * k) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
