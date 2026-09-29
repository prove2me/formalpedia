-- Prove2me | Theorems.Thm_lean_workbook_plus_42019
-- name    : lean_workbook_plus_42019
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7d98c5a8-9281-4862-a98b-513d4e3ca044
-- statement:
--   Given $a, b, c >0$ . Prove that $\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{c+a} \le \frac{1}{2} (\frac{1}{a} + \frac{1}{b} + \frac{1}{c})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42019 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≤ 1 / 2 * (1 / a + 1 / b + 1 / c)   :=  by sorry
