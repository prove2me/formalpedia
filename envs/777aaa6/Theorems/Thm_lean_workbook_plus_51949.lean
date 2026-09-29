-- Prove2me | Theorems.Thm_lean_workbook_plus_51949
-- name    : lean_workbook_plus_51949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/bd03ea0b-1eca-423b-9905-dc2ab8b9db20
-- statement:
--   Let $x,y$ be reals such that $x^2+y^2\leq x+y .$ Prove that $x+y\leq 2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51949 (x y : ℝ) (h : x^2 + y^2 ≤ x + y) : x + y ≤ 2   :=  by sorry
