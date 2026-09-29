-- Prove2me | Theorems.Thm_lean_workbook_plus_62828
-- name    : lean_workbook_plus_62828
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a82b2d07-94b7-4d29-9cd5-72b6aeb4aa4b
-- statement:
--   Prove that for $ \forall n \in N^+ $, $4^n+n^4$ is not a prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62828 : ∀ n : ℕ, 0 < n → ¬ (Nat.Prime (4^n+n^4))   :=  by sorry
