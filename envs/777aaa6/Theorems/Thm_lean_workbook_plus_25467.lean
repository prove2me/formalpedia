-- Prove2me | Theorems.Thm_lean_workbook_plus_25467
-- name    : lean_workbook_plus_25467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5267c9d9-dfec-4c20-8301-18dfd1619e75
-- statement:
--   Let $a ,b ,c>0 $ and $\frac{b+c}{a}+ \frac{c+a}{b}=9. $ Prove that $$(a+b+c)\left( \frac{1}{a}+\frac{1}{b}+\frac{1}{c} \right) \geq \dfrac{88}{7}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25467 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (b + c) / a + (c + a) / b = 9) :
  (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 88 / 7   :=  by sorry
