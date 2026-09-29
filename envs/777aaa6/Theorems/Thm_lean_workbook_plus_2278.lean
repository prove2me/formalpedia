-- Prove2me | Theorems.Thm_lean_workbook_plus_2278
-- name    : lean_workbook_plus_2278
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/34750a09-7055-4d1a-9be8-da278474cbb4
-- statement:
--   Prove that for any prime $p\ge5$, there exists a prime $q$ such that $p<q<2p-2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2278 (p : ℕ) (hp : 5 ≤ p) (hp' : Nat.Prime p) : 
  ∃ q : ℕ, p < q ∧ q < 2 * p - 2   :=  by sorry
