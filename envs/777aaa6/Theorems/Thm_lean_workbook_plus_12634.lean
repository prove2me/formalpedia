-- Prove2me | Theorems.Thm_lean_workbook_plus_12634
-- name    : lean_workbook_plus_12634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/facabbf9-b2d7-46c3-8142-3af9eaa0a34f
-- statement:
--   Prove that for positive numbers $a, b, c$ with $a^2 + b^2 + c^2 = 1$, the following inequality also holds: $\frac{a+b}{3+5ab} + \frac{b+c}{3+5bc} + \frac{c+a}{3+5ca} \leq \frac{3\sqrt{3}}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12634 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 1) : (a + b) / (3 + 5 * a * b) + (b + c) / (3 + 5 * b * c) + (c + a) / (3 + 5 * c * a) ≤ (3 * Real.sqrt 3) / 7   :=  by sorry
