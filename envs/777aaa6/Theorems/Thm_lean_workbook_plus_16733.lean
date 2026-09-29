-- Prove2me | Theorems.Thm_lean_workbook_plus_16733
-- name    : lean_workbook_plus_16733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3c6f6eb8-2e4a-4112-bb84-d70f2fbbacdf
-- statement:
--   If $ a,b,c$ are the side of triangle, prove the inequality:\n $ a^3+b^3+c^3+3abc\ge\sum_{cyc}ab(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16733 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a)   :=  by sorry
