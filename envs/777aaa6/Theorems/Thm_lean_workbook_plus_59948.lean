-- Prove2me | Theorems.Thm_lean_workbook_plus_59948
-- name    : lean_workbook_plus_59948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/7ef471a5-afd5-4e4b-a36a-fb4347fd22a6
-- statement:
--   Let $a,b,c>0$ . Prove that: \n $\frac{ab}{a+3b+2c}+\frac{bc}{b+3c+2a}+\frac{ca}{c+3a+2b}\le \frac{a+b+c}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59948 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) + c * a / (c + 3 * a + 2 * b)) ≤ (a + b + c) / 6   :=  by sorry
