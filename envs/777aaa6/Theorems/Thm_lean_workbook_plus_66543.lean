-- Prove2me | Theorems.Thm_lean_workbook_plus_66543
-- name    : lean_workbook_plus_66543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0453eaae-c900-4d50-b24c-d9cf209f978b
-- statement:
--   Prove that $\binom{2n}{n}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66543 (n : ℕ) : ∃ k : ℕ, (k : ℚ) = (Nat.choose (2 * n) n)   :=  by sorry
