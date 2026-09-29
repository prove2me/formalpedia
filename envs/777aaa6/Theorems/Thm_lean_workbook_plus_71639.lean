-- Prove2me | Theorems.Thm_lean_workbook_plus_71639
-- name    : lean_workbook_plus_71639
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/533e26ba-c205-4533-b536-de1ef2f77f20
-- statement:
--   Rewrite $\dfrac{x+1}{x^{2}}$ as $\dfrac{1}{x}+\dfrac{1}{x^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71639 (x : ℝ) (hx : x ≠ 0) : (x + 1) / x ^ 2 = 1 / x + 1 / x ^ 2   :=  by sorry
