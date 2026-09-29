-- Prove2me | Theorems.Thm_lean_workbook_plus_2410
-- name    : lean_workbook_plus_2410
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/98f54fa9-bdfe-486d-83f1-01b046765e08
-- statement:
--   Let $a,b,c>0$ $a^{2}+b^{2}+c^{2}=1$ . Prove that:\n $\sqrt{\frac{ab+2c^{2}}{1+ab-c^{2}}}+\sqrt{\frac{bc+2a^{2}}{1+bc-a^{2}}}+\sqrt{\frac{ca+2b^{2}}{1+ca-b^{2}}} \geq 2+ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2410  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  Real.sqrt ((ab + 2 * c^2) / (1 + ab - c^2)) + Real.sqrt ((bc + 2 * a^2) / (1 + bc - a^2)) + Real.sqrt ((ca + 2 * b^2) / (1 + ca - b^2)) ≥ 2 + ab + bc + ca   :=  by sorry
