-- Prove2me | Theorems.Thm_lean_workbook_plus_65508
-- name    : lean_workbook_plus_65508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c1f9bb01-20ae-4ef5-9c4a-45df49d1c5ae
-- statement:
--   Let $a,b,c>0$ and satify condition $3a+4c\geq 18$. Prove that: $a+b+c+\frac{6}{abc}\geq 7$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65508 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 3 * a + 4 * c ≥ 18) : a + b + c + 6 / (a * b * c) ≥ 7   :=  by sorry
