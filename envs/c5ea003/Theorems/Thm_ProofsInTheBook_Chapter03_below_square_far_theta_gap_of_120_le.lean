-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_below_square_far_theta_gap_of_120_le
-- name    : ProofsInTheBook.Chapter03.below_square_far_theta_gap_of_120_le
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:25:47.669891+00:00
-- url     : https://prove2.me/theorems/847619b1-6614-4774-a219-ceb684b7757c
-- title:
--   A Chebyshev–entropy gap below the square threshold
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $k\ge120$, $2k\le n$, and $n<k^2$. Put $r=\lfloor\sqrt n\rfloor$ and $M=\min(k,\lfloor n/3\rfloor)$, and assume $2r<M$. Define
--   $$H(n,k)=n\log n-k\log k-(n-k)\log(n-k),\qquad\vartheta(t)=\sum_{\substack{p\le t\\p\text{ prime}}}\log p.$$
--   Then
--   $$\frac r3\log n+M\log4-\vartheta(r)<H(n,k)+\frac{\log n-\log k-\log(n-k)}2+\frac{\log(2\pi)}2-2.$$
--   Logarithms are natural; r and M are integers before conversion to real numbers.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L1869. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.below_square_far_theta_gap_of_120_le
    {n k : ℕ} (hk120 : 120 ≤ k) (hn2k : 2 * k ≤ n)
    (_hnsq : n < k * k) (hfar : 2 * sqrt n < min k (n / 3)) :
    ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) <
      entropyTerm n k
        + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by sorry
