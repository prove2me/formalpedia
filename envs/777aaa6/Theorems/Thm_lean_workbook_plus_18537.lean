-- Prove2me | Theorems.Thm_lean_workbook_plus_18537
-- name    : lean_workbook_plus_18537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a9e68731-299a-446c-9748-464387d4b445
-- statement:
--   Prove that $\sum (a+b)^2 = 3\sum a^2 + 2\sum ab\leq 6\sum a^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18537 (a b c: ℝ) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
