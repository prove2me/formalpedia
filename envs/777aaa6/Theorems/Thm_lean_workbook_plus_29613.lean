-- Prove2me | Theorems.Thm_lean_workbook_plus_29613
-- name    : lean_workbook_plus_29613
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6e43f6ef-2a96-400a-a50c-6ba665e1cccb
-- statement:
--   Solve the equation $L(1 - e^{-\dfrac{L^2}{4}}) = 0$ for $L$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29613 (L : ℝ) : L * (1 - exp (-L^2 / 4)) = 0 ↔ L = 0   :=  by sorry
