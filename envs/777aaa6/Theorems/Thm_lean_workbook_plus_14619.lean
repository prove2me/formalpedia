-- Prove2me | Theorems.Thm_lean_workbook_plus_14619
-- name    : lean_workbook_plus_14619
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9d3361c5-b1e7-4e1f-9860-02ca9b5c7fcc
-- statement:
--   Prove that if two polynomials are equal for all real $x$, then their coefficients must be the same.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14619 (p q : Polynomial ℝ) (h : ∀ x, p.eval x = q.eval x) : p = q   :=  by sorry
