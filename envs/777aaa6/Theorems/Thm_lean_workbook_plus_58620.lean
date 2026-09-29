-- Prove2me | Theorems.Thm_lean_workbook_plus_58620
-- name    : lean_workbook_plus_58620
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/bbeb5c8f-6efb-4c86-a029-77b774e363f5
-- statement:
--   Find the closed form for the sequence $a_{n}$ defined by $a_{0}= 2$ , $a_{n+1}= 3a_{n}+1$ using generating functions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58620 (a : ℕ → ℕ) (a0 : a 0 = 2) (a_rec : ∀ n, a (n + 1) = 3 * a n + 1) : ∃ f : ℕ → ℕ, f n = a n   :=  by sorry
