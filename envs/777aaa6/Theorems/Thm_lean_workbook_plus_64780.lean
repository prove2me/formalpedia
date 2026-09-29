-- Prove2me | Theorems.Thm_lean_workbook_plus_64780
-- name    : lean_workbook_plus_64780
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7ab4ebdc-73d8-4d00-8236-3866b20cf662
-- statement:
--   Prove that $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}\le1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64780 : ∀ a b c : ℝ, (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) : ℝ) ≤ 1   :=  by sorry
