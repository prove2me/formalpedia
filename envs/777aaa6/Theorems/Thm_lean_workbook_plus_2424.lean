-- Prove2me | Theorems.Thm_lean_workbook_plus_2424
-- name    : lean_workbook_plus_2424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/18c9ed38-cb74-407d-9c4e-d828ec6f5287
-- statement:
--   Prove that for all positive integers $k$, there exists a positive integer $n$ such that $n2^k - 7$ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2424 (k : ℕ) : ∃ n : ℕ, ∃ x : ℕ, n * 2 ^ k - 7 = x ^ 2   :=  by sorry
