-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_interval_prime_or_exception_of_9_le_lt_20
-- name    : ProofsInTheBook.Chapter03.exists_interval_prime_or_exception_of_9_le_lt_20
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:35:56.02998+00:00
-- url     : https://prove2.me/theorems/9a827397-2a21-4bf4-b5ab-f6e13cd0e403
-- title:
--   Interval primes for 9 through 19 with three possible exceptions
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $9\le k<20$, $2k\le n$, and $n<k^2$. Either there is a prime p with
--   $$k<p,\qquad n-k<p\le n,$$
--   or $(n,k)$ is one of $(125,12)$, $(126,12)$, or $(126,13)$. The disjunction lists allowed exceptional parameter pairs; it does not assert here that no such prime exists at those pairs.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3624. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_interval_prime_or_exception_of_9_le_lt_20
    {n k : ℕ} (hk9 : 9 ≤ k) (hk20 : k < 20) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    (∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime)
      ∨ (n = 125 ∧ k = 12)
      ∨ (n = 126 ∧ k = 12)
      ∨ (n = 126 ∧ k = 13) := by sorry
