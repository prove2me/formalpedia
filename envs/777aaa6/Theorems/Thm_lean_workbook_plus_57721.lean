-- Prove2me | Theorems.Thm_lean_workbook_plus_57721
-- name    : lean_workbook_plus_57721
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/78486c7d-9fd2-4964-89be-342860363e83
-- statement:
--   Prove or disprove that the sequence of partial sums $S_{partial}=\sum_{n=1}^m\;\cos\,\sqrt n$ is bounded.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57721 (m : ℕ) : ∃ M, ∀ n ≤ m, |∑ k in Finset.range n, Real.cos (Real.sqrt k)| ≤ M   :=  by sorry
