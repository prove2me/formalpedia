-- Prove2me | Theorems.Thm_lean_workbook_plus_18225
-- name    : lean_workbook_plus_18225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1630cf0c-aa4f-4af7-950e-97b92cb503a7
-- statement:
--   Prove that $\frac{1}{2 - x} \ge \frac{1 + x^2}{2}$ for $0 \le x < 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18225 (x : ℝ) (hx : 0 ≤ x ∧ x < 2) : 1 / (2 - x) ≥ (1 + x ^ 2) / 2   :=  by sorry
