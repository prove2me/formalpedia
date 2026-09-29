-- Prove2me | Theorems.Thm_lean_workbook_plus_77947
-- name    : lean_workbook_plus_77947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/cffba863-a90d-4ae5-a0ba-bcba07b6a29b
-- statement:
--   If $x<y,$ then there are rationals $r,s$ with $x<r<s<y.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77947 (x y : ℝ) (h : x < y) : ∃ r s : ℚ, x < ↑r ∧ ↑r < s ∧ s < y   :=  by sorry
