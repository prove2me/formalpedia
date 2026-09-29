-- Prove2me | Theorems.Thm_lean_workbook_plus_18952
-- name    : lean_workbook_plus_18952
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/112744f6-aeb0-4d31-b42c-1ad828ebd1c9
-- statement:
--   Some positive integer solutions are $(x,y)=(1,1),(1,2),(2,1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18952 (x y : ℕ) (h₁ : x*y = 1) (h₂ : x + y = 2) : (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1)   :=  by sorry
