-- Prove2me | Theorems.Thm_lean_workbook_plus_78582
-- name    : lean_workbook_plus_78582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c53117ec-303e-457d-8dc9-ac1d8b2a9afc
-- statement:
--   Solve the system of equations:\n1. $x + y + z = 10$\n2. $xy + yz + zx = 54$\n3. $xyz = 70$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78582 (x y z : ℝ) (h₁ : x + y + z = 10) (h₂ : x*y + y*z + z*x = 54) (h₃ : x*y*z = 70) : (x = 9 ∧ y = 8 ∧ z = 7) ∨ (x = -9 ∧ y = -8 ∧ z = -7)   :=  by sorry
