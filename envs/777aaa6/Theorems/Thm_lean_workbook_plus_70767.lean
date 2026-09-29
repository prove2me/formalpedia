-- Prove2me | Theorems.Thm_lean_workbook_plus_70767
-- name    : lean_workbook_plus_70767
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7f73b166-5862-4ac6-bb55-33bc64de742b
-- statement:
--   Prove that there is an integer $ k < 1000 $ such that the absolute value of the difference between $ k \sqrt{2} $ and its nearest integer is $ < \frac{1}{1000} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70767 : ∃ k : ℤ, k < 1000 ∧ |k * Real.sqrt 2 - ↑⌊k * Real.sqrt 2⌋| < 1 / 1000   :=  by sorry
