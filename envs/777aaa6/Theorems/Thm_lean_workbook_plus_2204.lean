-- Prove2me | Theorems.Thm_lean_workbook_plus_2204
-- name    : lean_workbook_plus_2204
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a72db80e-1043-4b4d-911f-d554d52cb7a4
-- statement:
--   Assume $a,b,c$ are positive numbers, such that $ a(1-b) = b(1-c) = c(1-a) = \dfrac14 $. Prove that $a=b=c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * (1 - b) = 1 / 4) (hbc : b * (1 - c) = 1 / 4) (hca : c * (1 - a) = 1 / 4) : a = b ∧ b = c ∧ c = a   :=  by sorry
