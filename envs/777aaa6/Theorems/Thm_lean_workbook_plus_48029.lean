-- Prove2me | Theorems.Thm_lean_workbook_plus_48029
-- name    : lean_workbook_plus_48029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/81c7d305-c399-4e85-a62f-50f52c84b3e6
-- statement:
--   $ \Rightarrow \frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{a^2-ab+b^2} \ge \frac{3}{ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48029 (a b : ℝ) (hab : 0 < a ∧ 0 < b) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / (a ^ 2 - a * b + b ^ 2) ≥ 3 / (a * b)   :=  by sorry
