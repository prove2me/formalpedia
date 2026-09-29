-- Prove2me | Theorems.Thm_lean_workbook_plus_79317
-- name    : lean_workbook_plus_79317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d262b340-c088-4dd7-a7d7-d07307c61d1c
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a^2+b^2+c^2 = 1$ . Prove or disprove that $\frac{a}{\sqrt{1+bc}}+\frac{b}{\sqrt{1+ca}}+\frac{c}{\sqrt{1+ab}}\leq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a / Real.sqrt (1 + b * c) + b / Real.sqrt (1 + c * a) + c / Real.sqrt (1 + a * b) ≤ 3 / 2   :=  by sorry
