-- Prove2me | Theorems.Thm_lean_workbook_plus_78451
-- name    : lean_workbook_plus_78451
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3602d28e-0ae0-445c-ad86-22cfe514e3fe
-- statement:
--   Let $x=a-b,y=b-c,z=c-a$ , so that $x+y+z = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78451 (x y z : ℝ) (h : x = a - b ∧ y = b - c ∧ z = c - a) : x + y + z = 0   :=  by sorry
