-- Prove2me | Theorems.Thm_lean_workbook_plus_40606
-- name    : lean_workbook_plus_40606
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b2604bf2-c476-4f39-8772-7adcdfbc5844
-- statement:
--   Let $a;b;c;d>0$ .Prove that: \n\n $\frac{16}{1+abcd}\leq\frac{8}{\sqrt{abcd}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40606 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 16 / (1 + a * b * c * d) ≤ 8 / Real.sqrt (a * b * c * d)   :=  by sorry
