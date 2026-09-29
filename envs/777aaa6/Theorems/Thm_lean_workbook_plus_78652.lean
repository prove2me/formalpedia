-- Prove2me | Theorems.Thm_lean_workbook_plus_78652
-- name    : lean_workbook_plus_78652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b0e09d06-7234-4d47-aed7-a8163d8046c6
-- statement:
--   Prove that the sequence $\frac{1}{2^n}$ is bounded
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78652 : ∃ M, ∀ n, |(1:ℝ) / 2 ^ n| ≤ M   :=  by sorry
