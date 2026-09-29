-- Prove2me | Theorems.Thm_lean_workbook_plus_28443
-- name    : lean_workbook_plus_28443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/28dc7b7c-96d4-4953-994c-6a9e92743f05
-- statement:
--   Given $x, r \in \mathbb{R}$ such that $x^{5}-x^{3}+x = r$, prove that $x^{6}\ge 2r-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28443 (x r : ℝ) (h : x^5 - x^3 + x = r) : x^6 ≥ 2 * r - 1   :=  by sorry
