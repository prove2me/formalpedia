-- Prove2me | Theorems.Thm_lean_workbook_plus_9324
-- name    : lean_workbook_plus_9324
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5c695bb4-8738-47af-8d80-8b805b7477fc
-- statement:
--   Suppose $\\sin a + \\cos a = \\frac{1}{5}$ . What is the value of $\\sin^3 a + \\cos^3 a$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9324 (a : ℝ) (h : sin a + cos a = 1/5) : sin a ^ 3 + cos a ^ 3 = 37/125   :=  by sorry
