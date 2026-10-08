-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_pow_gap
-- name    : ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_of_pow_gap
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:31.985009+00:00
-- url     : https://prove2.me/theorems/e39678d3-1b4a-49b6-aca5-3d52f1c13bb8
-- title:
--   A power-gap criterion for a prime divisor above k
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k>0$ and $k\le n$. Let $q=\pi_\mathrm{pr}(k)$ be the number of primes at most k. Assume $q\le k$ and
--   $$k^k<n^{k-q}.$$
--   Then there is a prime p with $p>k$ and $p\mid\binom nk$. All powers in the premise are natural-number powers; k−q is natural subtraction, nonnegative by hypothesis.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L627. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_large_prime_factor_choose_of_pow_gap
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n)
    (hpi : Nat.primeCounting k ≤ k)
    (hpow : k ^ k < n ^ (k - Nat.primeCounting k)) :
    HasPrimeFactorAbove k (n.choose k) := by sorry
