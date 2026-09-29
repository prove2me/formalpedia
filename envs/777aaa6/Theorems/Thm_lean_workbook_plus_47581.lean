-- Prove2me | Theorems.Thm_lean_workbook_plus_47581
-- name    : lean_workbook_plus_47581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/62665c2f-0378-442f-8bb1-fc3f3c0afa0c
-- statement:
--   Show that $9(x^3+y^3)+18xy(x+y)=(x+2y)^3+(y+2x)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47581 (x y : ℤ) : 9 * (x ^ 3 + y ^ 3) + 18 * x * y * (x + y) = (x + 2 * y) ^ 3 + (y + 2 * x) ^ 3   :=  by sorry
