-- Prove2me | Theorems.Thm_lean_workbook_plus_65582
-- name    : lean_workbook_plus_65582
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9b638533-459d-48ac-a0ca-1bd07d339695
-- statement:
--   hello, you can solve this here $- \left( -{x}^{6}+\sqrt {3}{x}^{3}-1 \right) \left( {x}^{6}+\sqrt {3}{x}^{3}+1 \right) =0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65582 (x : ℝ) : -(-x^6 + Real.sqrt 3 * x^3 - 1) * (x^6 + Real.sqrt 3 * x^3 + 1) = 0   :=  by sorry
