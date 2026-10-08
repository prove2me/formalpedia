-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
-- name    : ProofsInTheBook.Chapter03.log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:27:09.209812+00:00
-- url     : https://prove2.me/theorems/d56d4990-c3c2-4c7a-9666-28fc09f29f20
-- title:
--   A Chebyshev-refined logarithmic binomial bound
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $0<n$, $k\le n$, $2k\le n$, and $6\le n$, and suppose all prime divisors of $\binom nk$ are at most $k$. Put $s=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$, and further assume $33\le s\le M$. Define $\vartheta(x)=\sum_{p\le x,\ p\text{ prime}}\log p$. Then
--   $$\log\binom nk\le\frac{s}{3}\log n+M\log4-\vartheta(s).$$
--   Logarithms are natural; $s,M$ are real-cast in this formula.
--
--   This is a conditional analytic estimate for excluding a binomial coefficient with only small prime divisors.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L917. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) := by sorry
