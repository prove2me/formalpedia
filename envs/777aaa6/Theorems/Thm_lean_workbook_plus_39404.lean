-- Prove2me | Theorems.Thm_lean_workbook_plus_39404
-- name    : lean_workbook_plus_39404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/264bafbb-2d41-4a5d-b164-42e280a6777d
-- statement:
--   If $x$ and $y$ are real numbers such that $x^2+y^2=1$ , find minimum and maximum of $xy(y^2-x^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39404 (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
  -1 ≤ x * y * (y ^ 2 - x ^ 2) ∧ x * y * (y ^ 2 - x ^ 2) ≤ 1   :=  by sorry
