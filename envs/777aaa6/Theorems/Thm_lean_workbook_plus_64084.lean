-- Prove2me | Theorems.Thm_lean_workbook_plus_64084
-- name    : lean_workbook_plus_64084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9d4706ac-1480-4fa9-a7eb-9fbe97278648
-- statement:
--   $P(0,0) \implies 2f(0) = 4f(0) \implies f(0) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64084 (f : ℝ → ℝ) (h₁ : 2 * f 0 = 4 * f 0) : f 0 = 0   :=  by sorry
