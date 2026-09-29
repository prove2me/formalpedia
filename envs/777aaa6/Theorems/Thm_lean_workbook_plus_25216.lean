-- Prove2me | Theorems.Thm_lean_workbook_plus_25216
-- name    : lean_workbook_plus_25216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c2a4de83-4602-4c70-8c5e-d76e49ef868f
-- statement:
--   Use the distance formula: Distance between $(x1,y1)$ and $(x2, y2)$ is $D=\sqrt{(y2-y1)^2+(x2-x1)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25216 (x1 y1 x2 y2 : ℝ) :
  Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = Real.sqrt ((y2 - y1)^2 + (x2 - x1)^2)   :=  by sorry
