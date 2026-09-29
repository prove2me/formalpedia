-- Prove2me | Theorems.Thm_lean_workbook_plus_1328
-- name    : lean_workbook_plus_1328
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6f2de5cc-761d-4d29-a736-2e9497475e01
-- statement:
--   Prove that $\frac{12ac}{5a+5b+2c}+\frac{12ba}{5b+5c+2a}+\frac{12cb}{5c+5a+2b}\leq a+b+c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1328 : ∀ a b c : ℝ, (12 * a * c / (5 * a + 5 * b + 2 * c) + 12 * b * a / (5 * b + 5 * c + 2 * a) + 12 * c * b / (5 * c + 5 * a + 2 * b)) ≤ a + b + c   :=  by sorry
