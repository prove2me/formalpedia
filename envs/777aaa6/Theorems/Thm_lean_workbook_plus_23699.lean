-- Prove2me | Theorems.Thm_lean_workbook_plus_23699
-- name    : lean_workbook_plus_23699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/97e86eec-431f-489b-9eb9-8be914b66c55
-- statement:
--   Prove that \((a+b)^2(c+d)^2+(a+c)^2(b+d)^2+(a+d)^2(b+c)^2\ge 3(a+b+c+d)(abc+bcd+cda+dab)\) where \(a,b,c,d>0\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23699 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) ^ 2 * (c + d) ^ 2 + (a + c) ^ 2 * (b + d) ^ 2 + (a + d) ^ 2 * (b + c) ^ 2 >= 3 * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
