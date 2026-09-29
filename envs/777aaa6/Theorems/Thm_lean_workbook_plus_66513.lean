-- Prove2me | Theorems.Thm_lean_workbook_plus_66513
-- name    : lean_workbook_plus_66513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/984c1e82-f8e2-4bf3-806d-35405afd05d9
-- statement:
--   Prove that $x(x^8+1)(x^3-1)+1>0$ for $x\in (0,1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66513 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x * (x^8 + 1) * (x^3 - 1) + 1 > 0   :=  by sorry
