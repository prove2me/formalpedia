-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
-- name    : ProofsInTheBook.Chapter03.choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:32.770249+00:00
-- url     : https://prove2.me/theorems/aea26e12-24e2-422c-ab58-c38874dc8dd9
-- title:
--   A split prime-product upper bound for binomial coefficients
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $n>0$, $k\le n$, $2k\le n$, and $n\ge6$. Suppose every prime divisor of $\binom nk$ is at most k. Put $r=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$. If $\pi_\mathrm{pr}(r)$ counts primes at most r, then
--   $$\binom nk\le n^{\pi_\mathrm{pr}(r)}\prod_{\substack{r<p\le M\\p\text{ prime}}}p.$$
--   An empty prime product equals 1.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L300. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * primeIntervalProduct (sqrt n) (min k (n / 3)) := by sorry
