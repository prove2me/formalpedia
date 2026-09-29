-- Prove2me | Theorems.Thm_lean_workbook_plus_79158
-- name    : lean_workbook_plus_79158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a8e9c99c-89a0-4bc2-9788-54e6a70bf4d4
-- statement:
--   Let x,y,z>0: xyz=1. Prove that: ${x^4} + {y^4} + {z^4} \ge x + y + z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79158 (x y z : ℝ) (hx : x>0 ∧ y>0 ∧ z>0 ∧ x*y*z=1) : x^4 + y^4 + z^4 >= x + y + z   :=  by sorry
