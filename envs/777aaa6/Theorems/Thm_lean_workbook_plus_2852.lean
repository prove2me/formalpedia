-- Prove2me | Theorems.Thm_lean_workbook_plus_2852
-- name    : lean_workbook_plus_2852
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8ce8b56d-35db-479e-a106-222701cecc7e
-- statement:
--   Prove that $\phi(n)$ and $\sigma(n)$ are multiplicative for coprime integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2852 {m n : ℕ} (hmn : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n   :=  by sorry
