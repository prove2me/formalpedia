-- Prove2me | Theorems.Thm_lean_workbook_plus_9473
-- name    : lean_workbook_plus_9473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a50e4c04-50a0-48d6-85fe-e6fd1984222d
-- statement:
--   We have $ \frac{x}{y}=\frac{6.5}{9.1}$ , so $ y=\frac{9.1}{6.5}x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9473 (x y : ℝ) (h₁ : x / y = 6.5 / 9.1) : y = 9.1 / 6.5 * x   :=  by sorry
