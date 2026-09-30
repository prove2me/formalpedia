-- Prove2me | solution 1 for lean_workbook_plus_12536
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:44.55776+00:00
-- url     : https://prove2.me/submissions/7d9a3137-294a-406c-8b56-f63db54c4d8e

import Mathlib.Analysis.Complex.Basic

/-- Brahmagupta–Fibonacci two-square identity (in the variant with `d` paired with `a`). -/
theorem solution {a b c d : ℝ} :
    (a ^ 2 + d ^ 2) * (c ^ 2 + b ^ 2) = (a * b + c * d) ^ 2 + (a * c - b * d) ^ 2 := by
  ring
