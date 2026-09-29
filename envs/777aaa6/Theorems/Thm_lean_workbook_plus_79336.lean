-- Prove2me | Theorems.Thm_lean_workbook_plus_79336
-- name    : lean_workbook_plus_79336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e67c9414-d012-49a9-9734-8e1ac4ce5a26
-- statement:
--   Find all the integral values of a, b and c such that $(1+\frac{1}{a})(1+\frac{1}{b})(1+\frac{1}{c}) = 3 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79336 (a b c : ℤ) (h : (1 + 1/a) * (1 + 1/b) * (1 + 1/c) = 3) : (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ b = 3 ∧ c = 2) ∨ (a = 2 ∧ b = 1 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 1) ∨ (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1)   :=  by sorry
