-- Prove2me | Theorems.Thm_WorkbookSource_problem_38666
-- name    : WorkbookSource.problem_38666
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:42.251672+00:00
-- url     : https://prove2.me/theorems/0943fba9-f1b7-4a56-a50b-250ff15637cb
-- title:
--   Ordering three large integer powers
-- statement:
--   Arrange the following numbers from greatest to least: $2^{110}$, $3^{75}$, $5^{49}$. Assume that $^$ means raised to (an exponent).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38666` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38666; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_38666 (x y z : ℝ) (hx : x = 2^110) (hy : y = 3^75) (hz : z = 5^49) : y > z ∧ z > x  :=  by sorry
