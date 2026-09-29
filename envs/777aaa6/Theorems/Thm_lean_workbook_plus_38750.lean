-- Prove2me | Theorems.Thm_lean_workbook_plus_38750
-- name    : lean_workbook_plus_38750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4a8243d8-e16a-4bd6-b66b-8bff885e8322
-- statement:
--   prove that : $x^4-y^4>4xy^3-4y^4$, given $x>y>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38750 (x y : ℝ) (hxy : x > y) (hy : y > 0) : x^4 - y^4 > 4 * x * y^3 - 4 * y^4   :=  by sorry
