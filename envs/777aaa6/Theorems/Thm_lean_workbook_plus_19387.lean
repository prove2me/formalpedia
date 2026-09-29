-- Prove2me | Theorems.Thm_lean_workbook_plus_19387
-- name    : lean_workbook_plus_19387
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0a120f9d-3f28-4f65-81b0-93094f9f1aad
-- statement:
--   If a number is a multiple of $4$, then it can be written as the product of two even numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19387 (n : ℕ) (h : n % 4 = 0) : ∃ a b, a % 2 = 0 ∧ b % 2 = 0 ∧ n = a * b   :=  by sorry
