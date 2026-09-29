-- Prove2me | Theorems.Thm_lean_workbook_plus_46268
-- name    : lean_workbook_plus_46268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/eddebd7c-7087-41ed-8ae7-fada9e56ccf4
-- statement:
--   Prove that \(a(b^2+c^2) + b(c^2+a^2) + c(a^2+b^2) \leq a^3+b^3+c^3 + 3abc\) for sides \(a, b, c\) of a triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46268 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b * b + c * c) + b * (c * c + a * a) + c * (a * a + b * b) ≤ a * a * a + b * b * b + c * c * c + 3 * a * b * c   :=  by sorry
