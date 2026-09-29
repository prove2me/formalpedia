-- Prove2me | Theorems.Thm_lean_workbook_plus_61241
-- name    : lean_workbook_plus_61241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ae6ba9e3-d88d-4f95-b71f-193d6a6cec4d
-- statement:
--   If $a,b,c,d\in[0,1]$ then show that: $3(a+b+c+d)\le8+(a^3+b^3+c^3+d^3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61241 (a b c d : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1): 3 * (a + b + c + d) ≤ 8 + a^3 + b^3 + c^3 + d^3   :=  by sorry
