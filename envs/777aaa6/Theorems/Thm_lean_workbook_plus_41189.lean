-- Prove2me | Theorems.Thm_lean_workbook_plus_41189
-- name    : lean_workbook_plus_41189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1a478f4e-c198-4001-9409-b9beb114212b
-- statement:
--   What is the greatest common factor of $2^{15}+3^{15}$ and $2^{25}+3^{25}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41189 (a b : ℕ) : a = 2 ^ 15 + 3 ^ 15 ∧ b = 2 ^ 25 + 3 ^ 25 → a.gcd b = 275   :=  by sorry
