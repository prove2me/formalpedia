-- Prove2me | Theorems.Thm_lean_workbook_plus_67327
-- name    : lean_workbook_plus_67327
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e92717a6-5d19-46d5-b047-0773b90dd0c5
-- statement:
--   Given that $-1 < x, y < 1$ , show that $-1 < \frac{x + y}{1 + xy} < 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67327 (x y : ℝ) (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) : -1 < (x + y) / (1 + x * y) ∧ (x + y) / (1 + x * y) < 1   :=  by sorry
