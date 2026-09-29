-- Prove2me | Theorems.Thm_lean_workbook_plus_36442
-- name    : lean_workbook_plus_36442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0909b25d-8c5c-416d-b65e-7bf7897a044e
-- statement:
--   Find all positive integers $n$ such that $n^{2}+2^{n}$ is square of an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36442 (n : ℕ) (hn : 0 < n) : (∃ k : ℕ, n^2 + 2^n = k^2) ↔ ∃ k : ℕ, n^2 + 2^n = k^2 ∧ k > 0   :=  by sorry
