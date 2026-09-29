-- Prove2me | Theorems.Thm_lean_workbook_plus_66754
-- name    : lean_workbook_plus_66754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/87374592-8a8f-403e-88db-e25a1787b905
-- statement:
--   And so $x\in(\frac {4\sqrt 2}3,2]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66754 (x : ℝ) (hx : 4 * Real.sqrt 2 / 3 < x ∧ x ≤ 2) : x ∈ Set.Ioc (4 * Real.sqrt 2 / 3) 2   :=  by sorry
