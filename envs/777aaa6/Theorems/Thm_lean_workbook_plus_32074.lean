-- Prove2me | Theorems.Thm_lean_workbook_plus_32074
-- name    : lean_workbook_plus_32074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e8b742b2-f7e3-4a61-9487-9cc8423f8711
-- statement:
--   Prove that for all positive a and b, \\(\\frac{5a+b\\left(2+\\frac ba\\right)}{a+b}\\ge4\\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32074 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (5 * a + b * (2 + b / a)) / (a + b) ≥ 4   :=  by sorry
