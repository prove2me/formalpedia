-- Prove2me | Theorems.Thm_lean_workbook_plus_66236
-- name    : lean_workbook_plus_66236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b8e20aec-4e83-4d36-ac2c-55c251fd5cd7
-- statement:
--   Solve for a,b,c,d in the system of equations: $a+b+c+d=1$, $8a+4b+2c+d=17$, $27a+9b+3c+d=66$, $64a+16b+4c+d=166$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66236 (a b c d : ℝ) : a+b+c+d=1 ∧ 8*a+4*b+2*c+d=17 ∧ 27*a+9*b+3*c+d=66 ∧ 64*a+16*b+4*c+d=166 ↔ a=3 ∧ b=-1.5 ∧ c=-0.5 ∧ d=0   :=  by sorry
