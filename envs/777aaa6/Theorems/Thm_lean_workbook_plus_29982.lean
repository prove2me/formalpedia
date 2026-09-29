-- Prove2me | Theorems.Thm_lean_workbook_plus_29982
-- name    : lean_workbook_plus_29982
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/eb41e962-73a3-4e28-8ed7-e0502427c6f1
-- statement:
--   Prove that ${n \choose r} = {n \choose n-r}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29982 (n r : ℕ) (h₁ : n ≥ r) : choose n r = choose n (n - r)   :=  by sorry
