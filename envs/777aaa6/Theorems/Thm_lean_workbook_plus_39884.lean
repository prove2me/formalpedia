-- Prove2me | Theorems.Thm_lean_workbook_plus_39884
-- name    : lean_workbook_plus_39884
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4f5f8ac8-abaa-4cba-b7de-4237585260b9
-- statement:
--   Prove that $x(x^3-6x+9)\le4 $ for $x\in{[0,1]}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39884 : ∀ x : ℝ, x ∈ Set.Icc 0 1 → x * (x ^ 3 - 6 * x + 9) ≤ 4   :=  by sorry
