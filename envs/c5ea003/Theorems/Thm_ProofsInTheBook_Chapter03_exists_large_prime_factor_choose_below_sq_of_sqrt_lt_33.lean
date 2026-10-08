-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:19.84093+00:00
-- url     : https://prove2.me/theorems/83d721c6-d3d7-455e-8da4-8e4745c921fe
-- title:
--   A prime divisor above k when the integer square root is below 33
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\ge9$, $2k\le n$, $n<k^2$, and $\lfloor\sqrt n\rfloor<33$. Then there is a prime p satisfying
--   $$p>k,\qquad p\mid\binom nk.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3762. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : sqrt n < 33) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
