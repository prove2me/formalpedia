-- Prove2me | Theorems.Thm_lean_workbook_plus_27582
-- name    : lean_workbook_plus_27582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/139f9bbc-a3c1-4b34-a195-3134b96c9d27
-- statement:
--   Let $a,b,c >0$ with $a^2+b^2+c^2=1$ . Prove that: $\frac{a}{1-a^2}+\frac{b}{1-b^2}+\frac{c}{1-c^2} \ge \frac{3 \sqrt{3}}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27582 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ 3 * Real.sqrt 3 / 2   :=  by sorry
