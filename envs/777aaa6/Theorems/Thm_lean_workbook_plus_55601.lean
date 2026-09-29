-- Prove2me | Theorems.Thm_lean_workbook_plus_55601
-- name    : lean_workbook_plus_55601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3b1c6ac6-5b63-4516-aa42-82c67a67b720
-- statement:
--   Prove that any bounded sequence in $\mathbb{R}$ has a limit point.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55601 (b : ℕ → ℝ) (h₁ : ∃ a, ∀ n, |b n| < a) : ∃ a, a ∈ {a : ℝ | ∃ n, b n ∈ Set.Icc a (a + 1)}   :=  by sorry
