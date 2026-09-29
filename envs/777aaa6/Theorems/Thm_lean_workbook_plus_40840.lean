-- Prove2me | Theorems.Thm_lean_workbook_plus_40840
-- name    : lean_workbook_plus_40840
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1146e7bd-a396-4420-ac52-91801262b0fb
-- statement:
--   Let $x$ be a real number with $x \ge 1$ . Prove that $x^3 - 5x^2 + 8x - 4 \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40840 (x : ℝ) (h : x ≥ 1) : x^3 - 5 * x^2 + 8 * x - 4 ≥ 0   :=  by sorry
