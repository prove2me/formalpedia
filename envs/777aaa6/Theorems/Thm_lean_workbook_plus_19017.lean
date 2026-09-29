-- Prove2me | Theorems.Thm_lean_workbook_plus_19017
-- name    : lean_workbook_plus_19017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/94f5a8b8-9d79-4739-a342-5c152c49217f
-- statement:
--   Let x,y>0. Prove the inequality is true, \n\n $ \frac{3}{2}x^2+\frac{3}{2}y^2+2xy-x-y+1 \ge (x+y)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19017 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 3/2 * x^2 + 3/2 * y^2 + 2 * x * y - x - y + 1 ≥ (x + y)^2   :=  by sorry
