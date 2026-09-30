-- Prove2me | solution 1 for lean_workbook_plus_78074
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:33.268443+00:00
-- url     : https://prove2.me/submissions/5b6f2220-8587-4c4f-97f5-39e8f5d314c6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ)
    (h₀ : a ^ 2 + b ^ 2 + (a - b) ^ 2 = c ^ 2 + d ^ 2 + (c - d) ^ 2) :
    a ^ 4 + b ^ 4 + (a - b) ^ 4 = c ^ 4 + d ^ 4 + (c - d) ^ 4 := by
  have hs := congrArg (fun x : ℝ => x ^ 2) h₀
  nlinarith only [hs]

#print axioms solution
