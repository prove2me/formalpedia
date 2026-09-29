-- Prove2me | Theorems.Thm_lean_workbook_plus_36562
-- name    : lean_workbook_plus_36562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9a84c89b-956e-470f-b91a-8e25789334a5
-- statement:
--   Derive the inequality $\frac{x}{1+nx^2} \leq \frac{1}{2\sqrt{n}}$ using the AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36562 (x : ℝ) (n : ℕ) (hn : n ≠ 0) : (x / (1 + n * x ^ 2)) ≤ (1 / (2 * Real.sqrt n))   :=  by sorry
