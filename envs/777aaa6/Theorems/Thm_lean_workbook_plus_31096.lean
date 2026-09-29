-- Prove2me | Theorems.Thm_lean_workbook_plus_31096
-- name    : lean_workbook_plus_31096
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d4983142-85aa-471b-84a4-f619e2beff88
-- statement:
--   prove that $ cos(A-B)+cos(B-C)+cos(C-A) \leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31096 (A B C : ℝ) : Real.cos (A - B) + Real.cos (B - C) + Real.cos (C - A) ≤ 3   :=  by sorry
