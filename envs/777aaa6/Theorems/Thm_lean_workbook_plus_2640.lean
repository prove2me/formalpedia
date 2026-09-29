-- Prove2me | Theorems.Thm_lean_workbook_plus_2640
-- name    : lean_workbook_plus_2640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1ca65c1f-0e5f-4e87-88d0-3d05771bc60e
-- statement:
--   if $a,b,c>0$ , $abc=1$ ,prove $a^3+b^3+c^3 >= ab+bc+ac$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2640 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1): a^3 + b^3 + c^3 >= a * b + b * c + a * c   :=  by sorry
