-- Prove2me | Theorems.Thm_lean_workbook_plus_34646
-- name    : lean_workbook_plus_34646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/09f24035-bd8e-4929-b010-b61e694546a6
-- statement:
--   $ ab\le\frac12(a^2+b^2)$ for positive $ a,b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34646 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * b ≤ (1 / 2) * (a ^ 2 + b ^ 2)   :=  by sorry
