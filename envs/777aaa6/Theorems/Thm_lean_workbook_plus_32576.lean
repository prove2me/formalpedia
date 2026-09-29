-- Prove2me | Theorems.Thm_lean_workbook_plus_32576
-- name    : lean_workbook_plus_32576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f0352f47-3943-43ca-922f-a995c0cae385
-- statement:
--   By Titu's lemma, $\frac{1}{a} +\frac{1}{b} + \frac{1}{c} \geq \frac{(3)^2}{a+b+c}= \frac{9}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32576 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c)   :=  by sorry
