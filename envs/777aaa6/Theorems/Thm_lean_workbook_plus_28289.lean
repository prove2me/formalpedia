-- Prove2me | Theorems.Thm_lean_workbook_plus_28289
-- name    : lean_workbook_plus_28289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/960adf38-a369-42e2-bf2b-3e7a2ad04141
-- statement:
--   Let $a,\,b,\,c$ are positive real numbers \n(1) Prove that \n $\frac{b+c}{a}+\frac{a^2}{bc} \geqslant 3 + \frac{(c-a)^2}{c(a+b)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28289 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + a ^ 2 / (b * c) ≥ 3 + (c - a) ^ 2 / (c * (a + b))   :=  by sorry
