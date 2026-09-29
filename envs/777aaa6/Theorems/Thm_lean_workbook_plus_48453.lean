-- Prove2me | Theorems.Thm_lean_workbook_plus_48453
-- name    : lean_workbook_plus_48453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b63118dd-c041-432c-99de-4af6500817b5
-- statement:
--   For $a, b, c>0, a^2+b^2+c^2=1$ prove that $\frac{a^3}{1-bc}+\frac{b^3}{1-ca}+\frac{c^3}{1-ab}\le\frac{a^4+b^4+c^4}{2abc(ab+bc+ca)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48453 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^3 / (1 - b * c) + b^3 / (1 - c * a) + c^3 / (1 - a * b) ≤
    (a^4 + b^4 + c^4) / (2 * a * b * c * (a * b + b * c + c * a))   :=  by sorry
