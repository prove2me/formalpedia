-- Prove2me | Theorems.Thm_lean_workbook_plus_49423
-- name    : lean_workbook_plus_49423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8a8b6187-c58b-49f6-af87-cf9465b646ee
-- statement:
--   Find all integers $(a,b)$ for which both $a^2-4b$ and $b^2-4a$ are perfect squares.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49423 (a b : ℤ) (h1 : ∃ x : ℤ, x^2 = a^2 - 4*b) (h2 : ∃ y : ℤ, y^2 = b^2 - 4*a) : (∃ x : ℤ, x^2 = a^2 - 4*b) ∧ (∃ y : ℤ, y^2 = b^2 - 4*a)   :=  by sorry
