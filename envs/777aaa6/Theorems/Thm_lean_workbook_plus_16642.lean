-- Prove2me | Theorems.Thm_lean_workbook_plus_16642
-- name    : lean_workbook_plus_16642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ef818866-09df-4c95-97ff-b331db0defcc
-- statement:
--   Let $a,b,c>0 $ and $a+b+c>1$ . Prove that \n $$\frac{1}{a+b+c-1}+\frac{b+c}{a} +\frac{c+a}{b}+\frac{a+b}{c}\ge 2+\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$$ \n $$\iff \frac{1}{a+b+c-1}+(a+b+c-1)\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)\ge 5$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16642 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (a + b + c - 1) + (b + c) / a + (c + a) / b + (a + b) / c ≥ 2 + 1 / a + 1 / b + 1 / c ↔ 1 / (a + b + c - 1) + (a + b + c - 1) * (1 / a + 1 / b + 1 / c) ≥ 5   :=  by sorry
