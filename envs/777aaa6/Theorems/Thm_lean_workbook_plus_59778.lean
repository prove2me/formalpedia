-- Prove2me | Theorems.Thm_lean_workbook_plus_59778
-- name    : lean_workbook_plus_59778
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/56a246f1-2fb5-4499-b29b-28affa42a213
-- statement:
--   We can prove that $a^2-a+1\geq\sqrt{\frac{a^4+1}{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59778 (a : ℝ) : a^2 - a + 1 ≥ Real.sqrt ((a^4 + 1)/2)   :=  by sorry
