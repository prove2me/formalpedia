-- Prove2me | Theorems.Thm_lean_workbook_plus_62470
-- name    : lean_workbook_plus_62470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2d867289-573e-404b-beca-225277888f5c
-- statement:
--   Given the function $f(x) = x^2$ with a domain of integers, what is the codomain and range?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62470 (f : ℤ → ℤ) (x : ℤ) (h₁ : f x = x^2) : ∃ y, y = x^2   :=  by sorry
