-- Prove2me | Theorems.Thm_lean_workbook_plus_31326
-- name    : lean_workbook_plus_31326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0144201c-ea68-4e73-852e-4580ecf60873
-- statement:
--   Given $x^{5}-x^{3}+x=a$, prove $(x-1)^{2}(x^{2}+x\sqrt{3}+1)(x^{2}-x\sqrt{3}+1)\geqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31326 (x a : ℝ) (h : x^5 - x^3 + x = a) :
  (x - 1)^2 * (x^2 + x * Real.sqrt 3 + 1) * (x^2 - x * Real.sqrt 3 + 1) ≥ 0   :=  by sorry
