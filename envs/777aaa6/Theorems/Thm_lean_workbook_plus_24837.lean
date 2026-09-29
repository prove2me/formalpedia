-- Prove2me | Theorems.Thm_lean_workbook_plus_24837
-- name    : lean_workbook_plus_24837
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b73ddf83-5bb4-427e-94cd-bbf4004b1c0e
-- statement:
--   Prove that if $n$ is a prime number, then $n^2 - n$ is divisible by 6.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24837 : ∀ n : ℕ, Nat.Prime n → 6 ∣ n^2 - n   :=  by sorry
