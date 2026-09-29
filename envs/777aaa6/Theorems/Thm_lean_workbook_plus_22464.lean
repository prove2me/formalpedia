-- Prove2me | Theorems.Thm_lean_workbook_plus_22464
-- name    : lean_workbook_plus_22464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/029d558f-06f5-4e78-8466-ac98a8d57ade
-- statement:
--   Given\n$x+5y-3z+6w=13$\n$2x+8y-2z+w=42$\n$3x-7y+11z-w=23$\nFind $w+x+y+z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22464 (x y z w : ℝ) (h₁ : x + 5*y - 3*z + 6*w = 13) (h₂ : 2*x + 8*y - 2*z + w = 42) (h₃ : 3*x - 7*y + 11*z - w = 23) : w + x + y + z = 13   :=  by sorry
