-- Prove2me | Theorems.Thm_lean_workbook_plus_27660
-- name    : lean_workbook_plus_27660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ac657758-a94b-4974-8cc6-2698ab5e1eb8
-- statement:
--   Your problem can be this: \n\n $\frac{ax+by}{a+b}\\ge \\frac{a+b}{\\frac{a}{x}+\\frac{b}{y}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27660 {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) :
  (a * x + b * y) / (a + b) ≥ (a + b) / (a / x + b / y)   :=  by sorry
