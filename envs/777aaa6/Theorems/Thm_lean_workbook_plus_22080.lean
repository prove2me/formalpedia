-- Prove2me | Theorems.Thm_lean_workbook_plus_22080
-- name    : lean_workbook_plus_22080
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/68807096-a091-4163-bfbe-2c73be0bd501
-- statement:
--   Derive the recursive relation $a_{n+1}=a_n^2-a_n+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22080 (a : ℕ → ℕ) (a0 : a 0 = 1) (a_succ : ∀ n, a (n + 1) = a n ^ 2 - a n + 1) : ∀ n, a (n + 1) = a n ^ 2 - a n + 1   :=  by sorry
