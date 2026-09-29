-- Prove2me | Theorems.Thm_lean_workbook_plus_26926
-- name    : lean_workbook_plus_26926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0bccdeae-37cc-4a1e-8033-31842322e7eb
-- statement:
--   Prove that for every prime number $ p$ we have $ p^m-1|p^n-1$ if $ m\mid n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26926 {p m n : ℕ} (hp : p.Prime) (h : m ∣ n) : p^m - 1 ∣ p^n - 1   :=  by sorry
