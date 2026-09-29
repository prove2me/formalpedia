-- Prove2me | Theorems.Thm_lean_workbook_plus_42472
-- name    : lean_workbook_plus_42472
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/0581b046-c90e-423b-b9a0-e400127d8b0f
-- statement:
--   Combining the inequalities $0<x$ and $x<2$ gives the range for $x$: $0<x<2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42472  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 2) :
  0 < x ∧ x < 2   :=  by sorry
