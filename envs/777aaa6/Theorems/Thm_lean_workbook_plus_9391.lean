-- Prove2me | Theorems.Thm_lean_workbook_plus_9391
-- name    : lean_workbook_plus_9391
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/753f4e8e-35cb-4bdd-a569-f2d4a807d7e5
-- statement:
--   $ \Leftrightarrow 12(x-y)^2(x^4+y^4+x^3y+xy^3+x^2y^2)-13x^2y^2(x-y)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9391 : ∀ x y : ℝ, 12*(x-y)^2*(x^4+y^4+x^3*y+x*y^3+x^2*y^2) - 13*x^2*y^2*(x-y)^2 ≥ 0   :=  by sorry
