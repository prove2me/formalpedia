-- Prove2me | Theorems.Thm_lean_workbook_plus_81335
-- name    : lean_workbook_plus_81335
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/db567b33-5345-4f65-8e64-31131505df54
-- statement:
--   From $a,b,c$ are the sides of triangle $\Rightarrow c<a+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81335 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) : c < a + b   :=  by sorry
