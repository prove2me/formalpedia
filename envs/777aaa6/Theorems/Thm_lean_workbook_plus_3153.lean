-- Prove2me | Theorems.Thm_lean_workbook_plus_3153
-- name    : lean_workbook_plus_3153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e2599a38-4b6d-49ad-ba5f-6a8d1c01ac4c
-- statement:
--   Let $x>0.$ Prove that:\n $\frac{2x}{x^{2}+4}+\frac{1}{3x^{2}+2}\leq \frac{3}{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3153 (x : ℝ) (hx : 0 < x) : (2 * x / (x ^ 2 + 4) + 1 / (3 * x ^ 2 + 2)) ≤ 3 / 5   :=  by sorry
