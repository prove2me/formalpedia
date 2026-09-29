-- Prove2me | Theorems.Thm_lean_workbook_plus_72942
-- name    : lean_workbook_plus_72942
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8e48efa4-4ddf-4ded-875d-1b144790599e
-- statement:
--   Solve the system of equations: $x + y + z = 3$, $xy + yz + zx = 9$, $xyz = 10$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72942 (x y z : ℝ) (h₁ : x + y + z = 3) (h₂ : x*y + y*z + z*x = 9) (h₃ : x*y*z = 10) : x = 2 ∧ y = 1 ∧ z = 0   :=  by sorry
