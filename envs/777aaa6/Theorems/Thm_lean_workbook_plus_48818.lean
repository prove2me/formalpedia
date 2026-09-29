-- Prove2me | Theorems.Thm_lean_workbook_plus_48818
-- name    : lean_workbook_plus_48818
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7cbe1fdf-f3ef-4a49-88c3-1e8276274f64
-- statement:
--   Prove that\n\n$$\sqrt{a^2-ab+b^2} \geq \frac{1}{2}(a+b)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48818 (a b : ℝ) : Real.sqrt (a ^ 2 - a * b + b ^ 2) ≥ (1 / 2) * (a + b)   :=  by sorry
