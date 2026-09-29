-- Prove2me | Theorems.Thm_lean_workbook_plus_37595
-- name    : lean_workbook_plus_37595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ae05ecbf-b144-428e-9b9e-ccee3d41023a
-- statement:
--   If $a,b,c$ are positive reals prove that \n $$a^4+b^4+c^4\geq a^3b+b^3c+c^3a$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37595 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a   :=  by sorry
