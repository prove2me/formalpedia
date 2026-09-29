-- Prove2me | Theorems.Thm_lean_workbook_plus_62457
-- name    : lean_workbook_plus_62457
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ed379ec4-477b-4aae-9004-f4e0e8843d5b
-- statement:
--   Let $x$ , $y$ and $z$ be real numbers such that $0 \leq x,y,z \leq 1$ . Prove that $xyz+(1-x)(1-y)(1-z)\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62457 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) : x*y*z + (1 - x)*(1 - y)*(1 - z) ≤ 1   :=  by sorry
