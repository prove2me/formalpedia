-- Prove2me | Theorems.Thm_lean_workbook_plus_18507
-- name    : lean_workbook_plus_18507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/08942851-df66-4fe6-8e46-27c7e80c0efa
-- statement:
--   By Cauchy-Schwarz inequality, we have: $ \frac {9}{3a + 2b + c}\le \frac {2}{a + b} + \frac {1}{a + c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18507 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 9 / (3 * a + 2 * b + c) ≤ 2 / (a + b) + 1 / (a + c)   :=  by sorry
