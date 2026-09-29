-- Prove2me | Theorems.Thm_lean_workbook_plus_55643
-- name    : lean_workbook_plus_55643
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/355e0588-f737-4f70-8843-acf83ca01fb2
-- statement:
--   Prove that if $n$ is a prime number, then $n^2 - n$ is divisible by 6.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55643 : ∀ n : ℕ, Nat.Prime n → 6 ∣ (n^2 - n)   :=  by sorry
