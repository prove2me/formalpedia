-- Prove2me | Theorems.Thm_lean_workbook_plus_7315
-- name    : lean_workbook_plus_7315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5b51b63b-b21c-450b-b371-397ac15cb980
-- statement:
--   Prove that equation $a^2 - b^2=ab - 1$ has infinitely many solutions, if $a,b$ are positive integers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7315 (a b : ℕ) (h₁ : 0 < a) (h₂ : 0 < b) : ∃ a b, a^2 - b^2 = a*b - 1   :=  by sorry
