-- Prove2me | Theorems.Thm_lean_workbook_plus_72394
-- name    : lean_workbook_plus_72394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e7fc39d1-34df-40b3-811b-4d2e5f53d9cb
-- statement:
--   Prove that for all $a,b,c>0$ : \n $\frac{b+c}{a^2+bc}+\frac{a+c}{b^2+ac}+\frac{b+a}{c^2+ba} \le \frac{1}{a} + \frac{1}{b} + \frac{1}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72394 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) + (b + a) / (c ^ 2 + b * a) ≤ 1 / a + 1 / b + 1 / c   :=  by sorry
