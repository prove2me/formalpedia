-- Prove2me | Theorems.Thm_lean_workbook_plus_60773
-- name    : lean_workbook_plus_60773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/919e7c02-8b35-4dcf-9f5a-3ebdd5711aa1
-- statement:
--   Cut Dedekind, or simply, cut, is defined as every pair $(E, D)$ of non-empty sets of rational numbers whose union is Q and such that every element of $E$ is less than any element from $D$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60773 : ∀ E D : Set ℚ, (E ∪ D = ℚ ∧ E ≠ ∅ ∧ D ≠ ∅ ∧ ∀ e ∈ E, ∀ d ∈ D, e < d) ↔ E ∪ D = ℚ ∧ E ≠ ∅ ∧ D ≠ ∅ ∧ ∀ e ∈ E, ∀ d ∈ D, e < d   :=  by sorry
