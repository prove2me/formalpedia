-- Prove2me | Theorems.Thm_lean_workbook_plus_66139
-- name    : lean_workbook_plus_66139
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/39b85207-db18-41f1-b82b-ae7929327426
-- statement:
--   $f(x)=c\quad\text{constant}\quad\forall x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66139 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∃ k, f k = c   :=  by sorry
