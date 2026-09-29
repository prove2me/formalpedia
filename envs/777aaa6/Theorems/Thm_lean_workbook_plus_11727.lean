-- Prove2me | Theorems.Thm_lean_workbook_plus_11727
-- name    : lean_workbook_plus_11727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bb41a018-1d32-4c7b-ba53-817188e6d4b8
-- statement:
--   Given any two real numbers $x<y$ , prove that we can find a rational number $q$ such that $x<q<y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11727 (x y : ℝ) (h : x < y) : ∃ q : ℚ, x < q ∧ ↑q < y   :=  by sorry
