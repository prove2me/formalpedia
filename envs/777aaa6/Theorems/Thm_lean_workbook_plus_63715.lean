-- Prove2me | Theorems.Thm_lean_workbook_plus_63715
-- name    : lean_workbook_plus_63715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/475a734a-bdba-46cd-89e8-375794da2157
-- statement:
--   Set $A$ consists of the numbers from $5$ through $10$ , and set $B$ consists of the numbers from $1$ through $6$ , inclusive. How many numbers are in $A$ or $B$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63715 (A B : Finset ℕ) : A = {5, 6, 7, 8, 9, 10} ∧ B = {1, 2, 3, 4, 5, 6} → A ∪ B = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}   :=  by sorry
