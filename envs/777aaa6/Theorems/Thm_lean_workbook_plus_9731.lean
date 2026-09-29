-- Prove2me | Theorems.Thm_lean_workbook_plus_9731
-- name    : lean_workbook_plus_9731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d1caace6-520f-476e-ac8e-c239ed8d31dd
-- statement:
--   For all integers $n$ , $|n| > 2$ , $(2n^2+n-2)^2<4(n^4+n^3+1) < (2n^2+n)^2\,.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9731 (n : ℤ) (hn : abs n > 2) : (2 * n ^ 2 + n - 2) ^ 2 < 4 * (n ^ 4 + n ^ 3 + 1) ∧ 4 * (n ^ 4 + n ^ 3 + 1) < (2 * n ^ 2 + n) ^ 2   :=  by sorry
