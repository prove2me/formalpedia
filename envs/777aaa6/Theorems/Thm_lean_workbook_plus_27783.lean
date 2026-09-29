-- Prove2me | Theorems.Thm_lean_workbook_plus_27783
-- name    : lean_workbook_plus_27783
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c261f4e8-123d-4481-9e3e-4b2bfb2aabef
-- statement:
--   Find the solutions to the equation $\sin(7x) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27783 : ∀ x : ℝ, sin (7 * x) = 0 ↔ ∃ k : ℤ, x = k * π / 7   :=  by sorry
