-- Prove2me | Theorems.Thm_lean_workbook_plus_70508
-- name    : lean_workbook_plus_70508
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/caea41ad-b31c-4ee5-a5d2-6b6eac11550d
-- statement:
--   Prove $\binom{n}{r}$ is an integer using Pascal's identity and simple induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70508 (n r : ℕ) : ∃ k, (k : ℚ) = choose n r   :=  by sorry
