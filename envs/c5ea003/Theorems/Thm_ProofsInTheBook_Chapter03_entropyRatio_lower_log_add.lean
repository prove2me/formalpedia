-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_entropyRatio_lower_log_add
-- name    : ProofsInTheBook.Chapter03.entropyRatio_lower_log_add
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:23.735602+00:00
-- url     : https://prove2.me/theorems/50323e1d-064d-4455-9c0e-eb8625809c75
-- title:
--   A lower bound for the entropy ratio
-- statement:
--   For every real $x>1$,
--   $$\log x+1-\frac1x\le x\log x-(x-1)\log(x-1).$$
--   The logarithm is natural.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L1111. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.entropyRatio_lower_log_add
    {x : ℝ} (hx : 1 < x) :
    Real.log x + 1 - 1 / x ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by sorry
