-- Prove2me | Theorems.Thm_lean_workbook_plus_4940
-- name    : lean_workbook_plus_4940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/66fb431b-462b-452a-9929-e9745b0837e6
-- statement:
--   Find the real numbers $x,\ y,\ z$ such that $x+y+z=xy+yz+zx=3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4940 (x y z : ℝ) (h₁ : x + y + z = 3) (h₂ : x*y + y*z + z*x = 3) : x = 1 ∧ y = 1 ∧ z = 1   :=  by sorry
