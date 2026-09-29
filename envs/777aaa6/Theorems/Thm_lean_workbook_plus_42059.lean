-- Prove2me | Theorems.Thm_lean_workbook_plus_42059
-- name    : lean_workbook_plus_42059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/46964f3b-97e1-4927-82c0-23ab207be7d8
-- statement:
--   Prove $y^{n}-1\geqslant n(y-1)$ for $y>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42059 (y : ℝ) (n : ℕ) (hy : y > 0) : y ^ n - 1 ≥ n * (y - 1)   :=  by sorry
