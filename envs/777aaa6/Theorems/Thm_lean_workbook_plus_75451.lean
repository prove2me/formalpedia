-- Prove2me | Theorems.Thm_lean_workbook_plus_75451
-- name    : lean_workbook_plus_75451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a9614d0a-9c41-4ffb-b5db-778296f0b267
-- statement:
--   $x^5-y^5=(x-y)(x^4+x^3y+x^2y^2+xy^3+y^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75451 (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4)   :=  by sorry
