-- Prove2me | Theorems.Thm_lean_workbook_plus_60713
-- name    : lean_workbook_plus_60713
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9a22931c-9a6e-4377-b259-0363f7126832
-- statement:
--   prove or disprove $a^3+b^3+c^3\geq{a^2+b^2+c^2}$ given $a,b,c>0$ and $abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60713 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
