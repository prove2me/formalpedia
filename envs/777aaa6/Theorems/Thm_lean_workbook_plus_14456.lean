-- Prove2me | Theorems.Thm_lean_workbook_plus_14456
-- name    : lean_workbook_plus_14456
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b107a33d-81d7-4db9-b592-7bb874543785
-- statement:
--   Let $ a,b,c\ge 0$ such that: \n $ a^2+c^2=1,b^2+2b(a+c)=6$ \nProve that: $ b(a-c)\ge 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14456 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a^2 + c^2 = 1) (hbc : b^2 + 2 * b * (a + c) = 6) : b * (a - c) ≥ 4   :=  by sorry
