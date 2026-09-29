-- Prove2me | Theorems.Thm_lean_workbook_plus_25053
-- name    : lean_workbook_plus_25053
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1a95443a-7416-432b-80e0-d3065712bced
-- statement:
--   $ \left( 1+x \right) \left( x+3 \right) \left( x+9 \right) \left( x+11 \right) \left( x+14 \right) \geq 14400\,x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25053 : ∀ x : ℝ, (1 + x) * (x + 3) * (x + 9) * (x + 11) * (x + 14) ≥ 14400 * x   :=  by sorry
