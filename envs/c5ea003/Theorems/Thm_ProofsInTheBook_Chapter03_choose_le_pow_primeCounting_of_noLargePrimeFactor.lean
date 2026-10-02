-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_choose_le_pow_primeCounting_of_noLargePrimeFactor
-- name    : ProofsInTheBook.Chapter03.choose_le_pow_primeCounting_of_noLargePrimeFactor
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:20.085464+00:00
-- url     : https://prove2.me/theorems/cb776e6d-94e4-409d-8149-5317a940b3c6
-- title:
--   A prime-counting upper bound under bounded prime factors
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $n>0$ and $k\le n$. Suppose every prime divisor of $\binom nk$ is at most k. Writing $\pi_\mathrm{pr}(k)$ for the number of primes at most k, one has
--   $$\binom nk\le n^{\pi_\mathrm{pr}(k)}.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L168. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.choose_le_pow_primeCounting_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting k := by sorry
