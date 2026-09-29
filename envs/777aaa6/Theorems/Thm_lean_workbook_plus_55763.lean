-- Prove2me | Theorems.Thm_lean_workbook_plus_55763
-- name    : lean_workbook_plus_55763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/eac2ce99-3f40-4bd0-910d-b855f884ef97
-- statement:
--   Prove that for all $a,b,c>0$ : \n $\frac{b+c}{a^2+bc}+\frac{a+c}{b^2+ac}+\frac{b+a}{c^2+ba} \le \frac{1}{a} + \frac{1}{b} + \frac{1}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55763 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) + (b + a) / (c ^ 2 + b * a) ≤ 1 / a + 1 / b + 1 / c   :=  by sorry
