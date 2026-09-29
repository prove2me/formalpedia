-- Prove2me | Theorems.Thm_lean_workbook_plus_52702
-- name    : lean_workbook_plus_52702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e1181087-be2d-462a-9e33-f9f03b046e4c
-- statement:
--   Let $a,b,c>0$ such that\n\n $$\frac{a}{a+5b+3c}+\frac{b}{b+5c+3a}+\frac{c}{c+5a+3b}\ge \frac13 $$\n\nProve the inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52702 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 5 * b + 3 * c) + b / (b + 5 * c + 3 * a) + c / (c + 5 * a + 3 * b) ≥ 1 / 3)   :=  by sorry
