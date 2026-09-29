-- Prove2me | Theorems.Thm_lean_workbook_plus_34977
-- name    : lean_workbook_plus_34977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c2725d49-efd2-417d-a8d1-7d3998c29a1b
-- statement:
--   $\gcd(x,y) = 1 \Rightarrow \exists a,b$ such that $ax + by = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34977 (x y : ℤ) (hxy: gcd x y = 1) : ∃ a b: ℤ, a*x + b*y = 1   :=  by sorry
