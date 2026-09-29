-- Prove2me | Theorems.Thm_lean_workbook_plus_82150
-- name    : lean_workbook_plus_82150
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c2026bd7-75a9-453d-adeb-9f4289791680
-- statement:
--   Since $0 < x < 1$ , we get: $\sum_{k=0}^{+\infty}x^{2^{n+1} \cdot k} = \frac{1}{1-x^{2^{n+1}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82150 (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
  (∑' k : ℕ, x^(2^(n+1) * k)) = 1 / (1 - x^(2^(n+1)))   :=  by sorry
