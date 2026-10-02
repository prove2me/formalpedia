-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:19.754328+00:00
-- url     : https://prove2.me/theorems/be8faec8-c294-462c-a8d0-5c32afc2ed2b
-- title:
--   A square-threshold and prime-counting criterion for a large prime divisor
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $1<k$, $k\le n$, and $k^2\le n$. Suppose
--   $$2\pi_\mathrm{pr}(k)<k,$$
--   where $\pi_\mathrm{pr}(k)$ counts primes at most k. Then a prime p exists with $p>k$ and $p\mid\binom nk$.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L713. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    {n k : ℕ} (hk1 : 1 < k) (hkn : k ≤ n) (hsq : k * k ≤ n)
    (hpi : 2 * Nat.primeCounting k < k) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
