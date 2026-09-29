-- Prove2me | Theorems.Thm_lean_workbook_plus_49677
-- name    : lean_workbook_plus_49677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1405bfc6-1cd1-4487-95f2-48e9e73eb778
-- statement:
--   If $ x=y$ then from the relation $ x^3+y^3=x-y$ we can receive that $ x=y=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49677  (x y : ℝ)
  (h₀ : x = y)
  (h₁ : x^3 + y^3 = x - y) :
  x = 0 ∧ y = 0   :=  by sorry
