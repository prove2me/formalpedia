-- Prove2me | Theorems.Thm_lean_workbook_plus_72775
-- name    : lean_workbook_plus_72775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/707e8f32-2253-4ac5-a641-5d0d8eed3c7f
-- statement:
--   Find roots of equation $ x^7 + x^4 + x^3 + x + 1 = 0 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72775 : ∀ x : ℂ, x^7 + x^4 + x^3 + x + 1 = 0 ↔ x = -1 ∨ x = 1 ∨ x = -Complex.exp (2*π*Complex.I/3) ∨ x = -Complex.exp (4*π*Complex.I/3)   :=  by sorry
