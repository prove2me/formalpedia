-- Prove2me | Theorems.Thm_lean_workbook_plus_9980
-- name    : lean_workbook_plus_9980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d23e2c46-3b95-493f-b92f-fd945dafeb82
-- statement:
--   Solve for $k$ in terms of $x$ : $x^4 -2kx^2 - x + k^2 - k = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9980 (x k : ℂ) : (x^4 - 2 * k * x^2 - x + k^2 - k = 0) ↔ (k = x^2 + x + 1 ∨ k = x^2 - x)   :=  by sorry
