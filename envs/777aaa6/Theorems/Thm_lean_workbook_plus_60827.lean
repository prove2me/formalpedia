-- Prove2me | Theorems.Thm_lean_workbook_plus_60827
-- name    : lean_workbook_plus_60827
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/338edeaa-ab8e-421f-9515-dab25c295d67
-- statement:
--   $b \mod{5} \in \{0, 1, 4\}$ and $b \mod{7} \in \{0, 3, 4\}.$ Thus, $b \in \{0, 4, 10, 11, 14, 21, 24, 25\}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60827 (b : ℕ) (h1 : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 4) (h2 : b % 7 = 0 ∨ b % 7 = 3 ∨ b % 7 = 4) : ∃ k : ℕ, b = 0 + k*5 ∨ b = 4 + k*5 ∨ b = 10 + k*5 ∨ b = 11 + k*5 ∨ b = 14 + k*5 ∨ b = 21 + k*5 ∨ b = 24 + k*5 ∨ b = 25 + k*5   :=  by sorry
