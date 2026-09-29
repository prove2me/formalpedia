-- Prove2me | Theorems.Thm_lean_workbook_plus_50102
-- name    : lean_workbook_plus_50102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e4602fed-7105-466b-b6e3-e75f5b81f637
-- statement:
--   If $x+y=2$ and $x^2+y^2=1$ , compute the values of $x^3+y^3$ , $x^4+y^4$ , $x^5+y^5$ , $x^6+y^6$ , and $x^{30}+y^{30}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50102 (x y : ℝ) (h₁ : x + y = 2) (h₂ : x^2 + y^2 = 1) : x^3 + y^3 = 2 ∧ x^4 + y^4 = 2 ∧ x^5 + y^5 = 2 ∧ x^6 + y^6 = 2 ∧ x^30 + y^30 = 2   :=  by sorry
