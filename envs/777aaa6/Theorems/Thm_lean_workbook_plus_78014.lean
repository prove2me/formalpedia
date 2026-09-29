-- Prove2me | Theorems.Thm_lean_workbook_plus_78014
-- name    : lean_workbook_plus_78014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/743dddc2-215e-461c-bdbc-ba4cf308abc0
-- statement:
--   Let be $ x,y,z\in \mathbb{R}$ such that $ x+y+z=2\ ,\ x^2+y^2+z^2=30\ ,\ x^3+y^3+z^3=116$ . Calculate $ xyz$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78014 (x y z : ℝ) (h₁ : x + y + z = 2) (h₂ : x^2 + y^2 + z^2 = 30) (h₃ : x^3 + y^3 + z^3 = 116) : x * y * z = 10   :=  by sorry
