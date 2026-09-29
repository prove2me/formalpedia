-- Prove2me | Theorems.Thm_lean_workbook_plus_57668
-- name    : lean_workbook_plus_57668
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a23090a8-880d-4f93-8d46-00a29ad01596
-- statement:
--   If $a,b,c$ are positive reals and $a^2+b^2+c^2=3$, then $ab+bc+ca\leq 1$ holds?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57668 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a * b + b * c + c * a ≤ 1   :=  by sorry
