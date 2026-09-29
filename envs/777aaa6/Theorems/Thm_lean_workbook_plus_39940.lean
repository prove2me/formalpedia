-- Prove2me | Theorems.Thm_lean_workbook_plus_39940
-- name    : lean_workbook_plus_39940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/26ae3713-2805-4dbc-94d5-0b2bececae53
-- statement:
--   Show that $\frac{x^2}{1 - x}+\frac{(1 - x)^2}{x} \ge 1$ for all real numbers $x$ , where $0 < x < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39940 (x : ℝ) (hx : 0 < x ∧ x < 1) : (x^2/(1 - x) + (1 - x)^2/x) ≥ 1   :=  by sorry
