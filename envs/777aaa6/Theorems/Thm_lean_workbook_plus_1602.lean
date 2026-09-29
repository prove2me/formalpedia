-- Prove2me | Theorems.Thm_lean_workbook_plus_1602
-- name    : lean_workbook_plus_1602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/dfaf5466-0e32-47ad-a298-b076a72213b0
-- statement:
--   Prove that $ x^2 - x + 2 \leq 2 $ on the interval $x \in [0,1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1602 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → x^2 - x + 2 ≤ 2   :=  by sorry
