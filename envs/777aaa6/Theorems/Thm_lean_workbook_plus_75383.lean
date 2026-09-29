-- Prove2me | Theorems.Thm_lean_workbook_plus_75383
-- name    : lean_workbook_plus_75383
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/379f4ce9-4cc8-43f1-b1c5-6e0e4a390651
-- statement:
--   Show that the equation $ x^{3}+y^{3}+z^{3}+t^{3}=1999$ has infinitely many solutions in quadruples $ (x,y,z,t)$ of integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75383 : ∃ c : ℤ, ∀ d : ℤ, ∃ x y z t : ℤ, x^3 + y^3 + z^3 + t^3 = 1999 ∧ x > d ∧ y > d ∧ z > d ∧ t > d   :=  by sorry
