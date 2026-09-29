-- Prove2me | Theorems.Thm_lean_workbook_plus_40380
-- name    : lean_workbook_plus_40380
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/60fe58a6-9182-4a75-8674-d558d88122a0
-- statement:
--   solBefore = 1 acre = x tons of potatoes\nAfter = 1 acre = x+4 tons of potatoes\n$360(x+4)=400x+640$\nx=20
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40380 (x : ℝ) : 360 * (x + 4) = 400 * x + 640 ↔ x = 20   :=  by sorry
