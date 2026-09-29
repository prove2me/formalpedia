-- Prove2me | Theorems.Thm_lean_workbook_plus_54904
-- name    : lean_workbook_plus_54904
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/51b62d6b-50c3-4fba-8857-17d97456a751
-- statement:
--   For a,b,c > 0 prove that $ \frac{1}{a^{2}}+\frac{1}{b^{2}}+\frac{1}{c^{2}}\ge \frac{a+b+c}{abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54904 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c)   :=  by sorry
