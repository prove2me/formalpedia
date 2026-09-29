-- Prove2me | Theorems.Thm_lean_workbook_plus_67020
-- name    : lean_workbook_plus_67020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/44ef8f41-273f-4cc3-ae1b-337da1ab6b2c
-- statement:
--   Can the sequence be defined as $x_n=\frac{1}{4-n},\ \left(\forall\right)\ n\in N^*,\ n\ne 4\ !$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67020 : ∃ x : ℕ → ℝ, ∀ n : ℕ, n ≠ 4 ∧ n > 0 → x n = 1 / (4 - n)   :=  by sorry
