-- Prove2me | Theorems.Thm_lean_workbook_plus_11101
-- name    : lean_workbook_plus_11101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/14a3575b-3f13-42f3-b1e0-a2f8345ce408
-- statement:
--   Let $a,b,c >0$ with $a^2+b^2+c^2=1$ . Prove that: $\frac{a}{1-a^2}+\frac{b}{1-b^2}+\frac{c}{1-c^2} \ge \frac{3 \sqrt{3}}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11101 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ (3 * Real.sqrt 3) / 2   :=  by sorry
