-- Prove2me | Theorems.Thm_lean_workbook_plus_4033
-- name    : lean_workbook_plus_4033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/247f41e9-977c-468a-97eb-9099fe2a8335
-- statement:
--   prove that : $x^4+3y^4>4xy^3$, given $x>y>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4033 (x y : ℝ) (hxy : x > y) (hy : y > 0) : x^4 + 3*y^4 > 4*x*y^3   :=  by sorry
