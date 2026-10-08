-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
-- name    : ProofsInTheBook.Chapter03.log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:41.247974+00:00
-- url     : https://prove2.me/theorems/e4cabe4f-aaab-434a-b775-02d45b6d154f
-- title:
--   A logarithmic binomial bound under a prime-factor restriction
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $0<n$, $k\le n$, $2k\le n$, and $6\le n$. Assume every prime divisor of $\binom nk$ is at most $k$. Set $s=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$. Write $\pi(t)=|\{p\in\mathbb N:p\le t\text{ and }p\text{ is prime}\}|$. Write $P(a,b)=\prod_{a<p\le b,\ p\text{ prime}}p$, with empty product $1$, and $\vartheta(x)=\sum_{p\le x,\ p\text{ prime}}\log p$.
--   Then
--   $$\log\binom nk\le\pi(s)\log n+\log P(s,M).$$
--   All logarithms are natural and all integer quantities inside them are cast to real numbers.
--
--   This conditional upper bound is a technical estimate, not the chapter’s final non-power theorem.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L418. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by sorry
