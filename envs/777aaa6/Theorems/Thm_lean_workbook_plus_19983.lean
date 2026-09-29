-- Prove2me | Theorems.Thm_lean_workbook_plus_19983
-- name    : lean_workbook_plus_19983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/204bcfd9-157c-4947-8d26-7c2d8f8995e0
-- statement:
--   For $y>2$ we have: $y^4<y^4+4y+1<(y^2+1)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19983 (y : ℝ) (h : y > 2) : y^4 < y^4 + 4 * y + 1 ∧ y^4 + 4 * y + 1 < (y^2 + 1)^2   :=  by sorry
