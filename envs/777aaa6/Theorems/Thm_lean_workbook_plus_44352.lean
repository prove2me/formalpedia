-- Prove2me | Theorems.Thm_lean_workbook_plus_44352
-- name    : lean_workbook_plus_44352
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/51686f26-f08b-4fa1-a9f6-6ab664b20510
-- statement:
--   If $(x+\sqrt{x^2+1})(y+\sqrt{y^2+1})=0$ then prove $x+y=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44352 (x y : ℝ) (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 0) : x + y = 0   :=  by sorry
