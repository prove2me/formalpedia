-- Prove2me | Theorems.Thm_lean_workbook_plus_75605
-- name    : lean_workbook_plus_75605
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/da14d4ce-5558-41d6-8758-1893ed373e8c
-- statement:
--   Prove that $X + \frac{1}{X} \le -2$ for all $x < 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75605 (x : ℝ) (hx : x < 0) : x + 1/x ≤ -2   :=  by sorry
