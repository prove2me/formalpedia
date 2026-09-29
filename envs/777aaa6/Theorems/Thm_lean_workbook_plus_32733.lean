-- Prove2me | Theorems.Thm_lean_workbook_plus_32733
-- name    : lean_workbook_plus_32733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/34947a3b-8963-4e0b-aeca-0ebbe2c6e658
-- statement:
--   Prove that there is no perfect square between $k^2$ and $(k+1)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32733 (k : ℕ) : ¬ ∃ x : ℕ, k^2 < x^2 ∧ x^2 < (k + 1)^2   :=  by sorry
