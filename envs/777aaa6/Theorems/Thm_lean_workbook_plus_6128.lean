-- Prove2me | Theorems.Thm_lean_workbook_plus_6128
-- name    : lean_workbook_plus_6128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/006b79f5-ca4b-42e8-9ee3-0688904830c7
-- statement:
--   Let $ a, b, c, d$ are positive real numbers such that $a+b\geq \frac{1}{3}(c+d)$ and $a^2+b^2=\frac{1}{3}(c^2+d^2).$ Prove that\n\n $$a^4+a^2b^2+b^4\leq \frac{4}{27}(c^4+c^2d^2+d^4)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6128 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b ≥ 1 / 3 * (c + d)) (h : a^2 + b^2 = 1 / 3 * (c^2 + d^2)) : a^4 + a^2 * b^2 + b^4 ≤ 4 / 27 * (c^4 + c^2 * d^2 + d^4)   :=  by sorry
