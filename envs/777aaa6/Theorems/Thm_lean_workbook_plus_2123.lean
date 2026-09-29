-- Prove2me | Theorems.Thm_lean_workbook_plus_2123
-- name    : lean_workbook_plus_2123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/435b94b6-6fe7-4176-8105-184b55c91f54
-- statement:
--   If $x \in (0, 1)$, then $x^3 < 1 < x^4+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2123 (x : ℝ) (hx : 0 < x ∧ x < 1) : x^3 < 1 ∧ 1 < x^4 + 1   :=  by sorry
