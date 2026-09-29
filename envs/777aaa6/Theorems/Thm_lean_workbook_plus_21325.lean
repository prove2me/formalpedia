-- Prove2me | Theorems.Thm_lean_workbook_plus_21325
-- name    : lean_workbook_plus_21325
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b11ece55-e205-4796-8751-a390253fdebc
-- statement:
--   $ \arcsin (\sin x) = x, 0 \le x <2\pi$ , right?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21325 : ∀ x : ℝ, 0 ≤ x ∧ x < 2 * π → arcsin (sin x) = x   :=  by sorry
