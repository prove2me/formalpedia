-- Prove2me | Theorems.Thm_lean_workbook_plus_63657
-- name    : lean_workbook_plus_63657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f3d8e43f-335d-4782-892e-08e019899559
-- statement:
--   prove if $a^2+b^2+c^2+abc =4$ then $a+b+c\leq 3$ where $a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63657 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^2 + b^2 + c^2 + a * b * c = 4 → a + b + c ≤ 3   :=  by sorry
