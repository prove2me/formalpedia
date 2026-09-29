-- Prove2me | Theorems.Thm_lean_workbook_plus_11176
-- name    : lean_workbook_plus_11176
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/63e505d6-36ae-4175-8223-98f2f93c7ab4
-- statement:
--   From Cauchy we have \n\n ${3[(a}^{2}+b^{2}+c^{2})+(b^{2}+c^{2}+d^{2})+(c^{2}+d^{2}+a^{2})+(d^{2}+a^{2}+b^{2})]\geq(a+b+c)^{2}+(b+c+d)^{2}+(c+d+a)^{2}+(d+a+b)^{2}$ \n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11176 {a b c d : ℝ} :
  3 * ((a^2 + b^2 + c^2) + (b^2 + c^2 + d^2) + (c^2 + d^2 + a^2) + (d^2 + a^2 + b^2)) ≥
  (a + b + c)^2 + (b + c + d)^2 + (c + d + a)^2 + (d + a + b)^2   :=  by sorry
