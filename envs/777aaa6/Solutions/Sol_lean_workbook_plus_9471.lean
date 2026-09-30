-- Prove2me | solution 1 for lean_workbook_plus_9471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:28.541826+00:00
-- url     : https://prove2.me/submissions/14ef3037-5212-49e8-b155-8ddf031b3263

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4*(a^2 - a*b + b^2) ≥ (a+b)^2 := by
  nlinarith [sq_nonneg (a - b)]
