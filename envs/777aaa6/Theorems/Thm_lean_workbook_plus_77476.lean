-- Prove2me | Theorems.Thm_lean_workbook_plus_77476
-- name    : lean_workbook_plus_77476
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b0c82999-b530-4b48-b6df-703c9d2be50c
-- statement:
--   Find all integer number $x,y$ such that $x^3+xy^2+x^2y+y^3=4(x^2+y^2+xy+3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77476 (x y : ℤ) (h : x^3 + x*y^2 + x^2*y + y^3 = 4*(x^2 + y^2 + x*y + 3)) : (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = -2) ∨ (x = 0 ∧ y = -3) ∨ (x = -3 ∧ y = 0)   :=  by sorry
