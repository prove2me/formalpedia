-- Prove2me | Theorems.Thm_lean_workbook_plus_3968
-- name    : lean_workbook_plus_3968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/80c16f8d-d3ac-4bea-a30a-5d6dff3f2ed5
-- statement:
--   Let $a, b, c > 0$ . Prove that: \n$$ (a+b)(b+c)(c+a) \geqslant \dfrac{2abc(a+b+c+1)^2}{ab+bc+ca+1}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3968 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a+b)*(b+c)*(c+a) ≥ (2*a*b*c*(a+b+c+1)^2)/(a*b+b*c+c*a+1)   :=  by sorry
