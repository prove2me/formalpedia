-- Prove2me | Theorems.Thm_lean_workbook_plus_12563
-- name    : lean_workbook_plus_12563
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3c517def-445e-4666-98da-ff8aa4d89863
-- statement:
--   Now $ 0 \le (1-x)x=-(x-\frac{1}{2})^2+\frac{1}{4} \le \frac{1}{4}$ for $ x \in [0,1]$ , so
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12563  (x : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : x ≤ 1) :
  0 ≤ (1 - x) * x ∧ (1 - x) * x ≤ 1 / 4   :=  by sorry
