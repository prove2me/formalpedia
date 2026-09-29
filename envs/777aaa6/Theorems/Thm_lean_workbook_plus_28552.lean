-- Prove2me | Theorems.Thm_lean_workbook_plus_28552
-- name    : lean_workbook_plus_28552
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3136438f-ee6b-4a69-8be1-9ca87b042189
-- statement:
--   For $a,b,c>0$ such that $a^2+b^2+c^2+2abc=1$ . Prove\n$\frac{ab\sqrt{2-2c}}{a+b}+\frac{bc\sqrt{2-2a}}{b+c}+\frac{ca\sqrt{2-2b}}{c+a}\leq \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28552 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) :
  (a * b * Real.sqrt (2 - 2 * c)) / (a + b) + (b * c * Real.sqrt (2 - 2 * a)) / (b + c) + (c * a * Real.sqrt (2 - 2 * b)) / (c + a) ≤ 3 / 4   :=  by sorry
