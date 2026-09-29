-- Prove2me | Theorems.Thm_lean_workbook_plus_40370
-- name    : lean_workbook_plus_40370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d46aa77c-6f78-41c9-b2e0-6db9d010c84a
-- statement:
--   Prove that: $12xy{\leq}4x(1-y)+9y(1-x)$ given $x,y{\ge}0$ and $x+y{\leq}1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40370 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y ≤ 1) :
  12 * x * y ≤ 4 * x * (1 - y) + 9 * y * (1 - x)   :=  by sorry
