-- Prove2me | Theorems.Thm_lean_workbook_plus_75279
-- name    : lean_workbook_plus_75279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/edab519a-b483-4ee2-8f06-04798f8f97ee
-- statement:
--   If $p|x^2+xy+y^2$, show that $p|(2x+y)^2+3y^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75279 (p x y : ℤ) : p ∣ x^2 + x*y + y^2 → p ∣ (2*x + y)^2 + 3*y^2   :=  by sorry
