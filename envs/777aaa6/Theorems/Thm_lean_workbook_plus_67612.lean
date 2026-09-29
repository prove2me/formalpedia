-- Prove2me | Theorems.Thm_lean_workbook_plus_67612
-- name    : lean_workbook_plus_67612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/05f0d8c5-5a47-42c9-b21b-226121654525
-- statement:
--   What is the correct ordering of the three numbers $\frac5{19}$ , $\frac7{21}$ , and $\frac9{23}$ , in increasing order?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67612 (a b c : ℚ) (h₁ : a = 5 / 19) (h₂ : b = 7 / 21) (h₃ : c = 9 / 23) : a < b ∧ b < c   :=  by sorry
