-- Prove2me | Theorems.Thm_lean_workbook_plus_36765
-- name    : lean_workbook_plus_36765
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/baefb439-6379-493e-9431-136071bac403
-- statement:
--   Prove that $1-nx > 0$ for $x < \frac{1}{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36765 (n : ℕ) (x : ℝ) (hx: x < 1/n) : 1 - n * x > 0   :=  by sorry
