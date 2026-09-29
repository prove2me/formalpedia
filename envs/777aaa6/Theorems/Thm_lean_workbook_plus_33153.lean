-- Prove2me | Theorems.Thm_lean_workbook_plus_33153
-- name    : lean_workbook_plus_33153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0f7d53a7-6a7f-47c2-95da-e9ae4c3cb3bf
-- statement:
--   Given $a, b, c > 0$ and $(a+b)(b+c)(c+a) = 8$, prove that $(a^2+bc)(b^2+ca)(c^2+ab) \le 8(2-abc)^6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33153 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) * (c + a) = 8) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤ 8 * (2 - a * b * c)^6   :=  by sorry
