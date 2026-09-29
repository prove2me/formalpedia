-- Prove2me | Theorems.Thm_lean_workbook_plus_2420
-- name    : lean_workbook_plus_2420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c00f09a1-d44e-4b8c-b90d-94dc7f70a42e
-- statement:
--   If $x,y$ are pozitive real numbers such that $x+y+xy=3$ .Prove that $x+y\geq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2420 (x y : ℝ) (hxy : 0 < x ∧ 0 < y) (h : x + y + x * y = 3) : x + y ≥ 2   :=  by sorry
