-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_below_square_B_core_large
-- name    : ProofsInTheBook.Chapter03.below_square_B_core_large
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:25:31.977196+00:00
-- url     : https://prove2.me/theorems/6601a242-5165-48ed-8899-89c1e0249647
-- title:
--   A logarithmic entropy estimate for x at least 31
-- statement:
--   Let $K,x\in\mathbb R$ satisfy $120\le K$, $31\le x$, and $x\le K/4+1$. Then
--   $$\frac{\sqrt{x/K}}{3}\log(Kx)+\min(1,x/3)\log4+\frac1{32}\le x\log x-(x-1)\log(x-1).$$
--   Here the square root is the real square root and logarithms are natural.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L1772. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.below_square_B_core_large {K x : ℝ}
    (_hK120 : 120 ≤ K) (hx31 : 31 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by sorry
