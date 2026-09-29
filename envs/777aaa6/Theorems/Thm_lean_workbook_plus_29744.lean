-- Prove2me | Theorems.Thm_lean_workbook_plus_29744
-- name    : lean_workbook_plus_29744
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c6dabe24-4285-4a87-ad8c-cced633d1e9c
-- statement:
--   Prove that if $p$ and $q$ are prime numbers greater than or equal to 5, then $p$ does not divide $2^q-1$ and $q$ does not divide $2^p-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29744 : ∀ p q : ℕ, p.Prime ∧ q.Prime ∧ p >= 5 ∧ q >= 5 → ¬ (p ∣ (2^q-1)) ∧ ¬ (q ∣ (2^p-1))   :=  by sorry
