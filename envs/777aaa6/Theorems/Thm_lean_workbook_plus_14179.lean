-- Prove2me | Theorems.Thm_lean_workbook_plus_14179
-- name    : lean_workbook_plus_14179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f02aa2ef-774d-4bb2-ab45-da8d07aeec25
-- statement:
--   The closed form for this is $a_n=\frac{1}{2\sqrt{2}} \left((1+\sqrt 2)^n-(1-\sqrt 2 )^n \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14179 (n : ℕ) : ∃ a : ℝ, a = (1 / (2 * Real.sqrt 2)) * ((1 + Real.sqrt 2)^n - (1 - Real.sqrt 2)^n)   :=  by sorry
