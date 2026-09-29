-- Prove2me | Theorems.Thm_lean_workbook_plus_69562
-- name    : lean_workbook_plus_69562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b791da8d-2377-4d0c-a8fa-652399493c62
-- statement:
--   Let $ a, b, c, d$ are positive real numbers such that $a+b\geq 2(c+d)$ and $a^2+b^2=2(c^2+d^2).$ Prove that\n\n $$a^4+a^2b^2+b^4\leq 3(c^4+c^2d^2+d^4)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69562 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b ≥ 2 * (c + d)) (h : a^2 + b^2 = 2 * (c^2 + d^2)) : a^4 + a^2 * b^2 + b^4 ≤ 3 * (c^4 + c^2 * d^2 + d^4)   :=  by sorry
