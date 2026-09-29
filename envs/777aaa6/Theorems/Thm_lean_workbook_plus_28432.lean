-- Prove2me | Theorems.Thm_lean_workbook_plus_28432
-- name    : lean_workbook_plus_28432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/113bd29a-ce1f-439f-ba98-22004a0d8492
-- statement:
--   and this proves the problem because we have: \n\n $\binom{n}{k}=\binom{n}{n-k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28432  (n k : ℕ)
  (h₀ : n ≥ k) :
  Nat.choose n k = Nat.choose n (n - k)   :=  by sorry
