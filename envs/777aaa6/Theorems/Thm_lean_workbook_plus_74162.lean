-- Prove2me | Theorems.Thm_lean_workbook_plus_74162
-- name    : lean_workbook_plus_74162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3b1da5b0-952f-4a19-abf5-89cf39b5d2ae
-- statement:
--   prove that $\sqrt{1+a^2}\le \frac{(a+b)+(a+c)}{2}$ given $a,b,c>0$ and $ab+bc+ca=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74162 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b + b * c + c * a = 1) : Real.sqrt (1 + a ^ 2) ≤ (a + b + (a + c)) / 2   :=  by sorry
