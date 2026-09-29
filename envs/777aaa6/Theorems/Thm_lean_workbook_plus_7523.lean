-- Prove2me | Theorems.Thm_lean_workbook_plus_7523
-- name    : lean_workbook_plus_7523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/81af79c6-65f3-4a85-9e2c-fd24ea0c0ab8
-- statement:
--   Looking at the equation mod $2$ , we get $xy\equiv 1\pmod 2$ and so both $x,y$ are odd
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7523  (x y : ℤ)
  (h₀ : x * y ≡ 1 [ZMOD 2]) :
  x % 2 = 1 ∧ y % 2 = 1   :=  by sorry
