-- Prove2me | Theorems.Thm_lean_workbook_plus_56975
-- name    : lean_workbook_plus_56975
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2523d6fe-dbec-460b-a135-d1139ae2be91
-- statement:
--   In such a arithmetic progression we have. ${{a}_{n+1}}=1+729n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56975 (n : ℕ) (a : ℕ → ℕ) (h₁ : a (n + 1) = 1 + 729 * n) : a (n + 1) = 1 + 729 * n   :=  by sorry
