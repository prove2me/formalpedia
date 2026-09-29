-- Prove2me | Theorems.Thm_lean_workbook_plus_62021
-- name    : lean_workbook_plus_62021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0a01831c-92ee-4d88-b2ac-e88466abead4
-- statement:
--   Given that $x$ and $y$ are real numbers such that $x+y=4$ find the minimum value of $x^2+y^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62021 (x y : ℝ) (h : x + y = 4) : 8 ≤ x ^ 2 + y ^ 2   :=  by sorry
