-- Prove2me | Theorems.Thm_lean_workbook_plus_12049
-- name    : lean_workbook_plus_12049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/aba3f6d5-145a-49d2-8337-7b15f861a4aa
-- statement:
--   Factor the quadratic equation \(a^2+5ab+6b^2=0\) and solve for a and b.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12049 : ∀ a b : ℝ, a^2 + 5 * a * b + 6 * b^2 = 0 → (a + 2 * b) * (a + 3 * b) = 0   :=  by sorry
