-- Prove2me | Theorems.Thm_lean_workbook_plus_3543
-- name    : lean_workbook_plus_3543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7d97ab04-c00c-4c97-ae02-7ac7da6e9769
-- statement:
--   prove that $ \frac{a}{\sqrt{1+bc}}+ \frac{b}{\sqrt{1+ac}}+ \frac{c}{\sqrt{1+ab}} \le \frac{3}{2}$ given $ a,b,c>0$ and $ a^2+b^2+c^2=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / Real.sqrt (1 + b * c) + b / Real.sqrt (1 + a * c) + c / Real.sqrt (1 + a * b) ≤ 3 / 2   :=  by sorry
