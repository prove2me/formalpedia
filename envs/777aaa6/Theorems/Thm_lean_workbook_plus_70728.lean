-- Prove2me | Theorems.Thm_lean_workbook_plus_70728
-- name    : lean_workbook_plus_70728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/152f9e57-857b-4feb-9199-5d0f2d0721b7
-- statement:
--   Prove that for real $a < b < c < d$ is $ (a+b+c+d)^2 - 8(ac + bd) > 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70728 (a b c d : ℝ) (h₁ : a < b ∧ b < c ∧ c < d) :  (a + b + c + d) ^ 2 - 8 * (a * c + b * d) > 0   :=  by sorry
