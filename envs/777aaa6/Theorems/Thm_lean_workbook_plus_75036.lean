-- Prove2me | Theorems.Thm_lean_workbook_plus_75036
-- name    : lean_workbook_plus_75036
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b4d7603b-ab4a-4fac-9bda-d92bfafa1235
-- statement:
--   Prove that if $x^2 + y^2 = 1$ and $x, y$ are real numbers, then $x + y \leq \sqrt{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75036 (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : x + y ≤ Real.sqrt 2   :=  by sorry
