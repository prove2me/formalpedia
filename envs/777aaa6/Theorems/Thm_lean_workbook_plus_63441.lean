-- Prove2me | Theorems.Thm_lean_workbook_plus_63441
-- name    : lean_workbook_plus_63441
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f0b0b308-7882-4b81-9c73-b17bc867613b
-- statement:
--   Given the function $f(x) = \frac{3x}{5} - \frac{6}{5}$, how do you shade the region that satisfies $y \ge f(x)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63441 (x y : ℝ) : y ≥ (3*x - 6) / 5 ↔ y ≥ 3*x/5 - 6/5   :=  by sorry
