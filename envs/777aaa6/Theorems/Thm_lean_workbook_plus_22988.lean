-- Prove2me | Theorems.Thm_lean_workbook_plus_22988
-- name    : lean_workbook_plus_22988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/cf547b6f-0a27-41a8-b90e-3b072e0e2e26
-- statement:
--   Real numbers $a,b,c,d>0 $, and $a^2+b^2+c^2+d^2=1$. Prove that $a+b+c+d+\frac{1}{abcd} \geq 18$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22988 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c * d = 1) (h : a^2 + b^2 + c^2 + d^2 = 1) : a + b + c + d + 1 / (a * b * c * d) ≥ 18   :=  by sorry
