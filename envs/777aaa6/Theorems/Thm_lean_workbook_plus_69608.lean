-- Prove2me | Theorems.Thm_lean_workbook_plus_69608
-- name    : lean_workbook_plus_69608
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c75584d9-1c5a-4896-ad9f-be84ab976087
-- statement:
--   The correct way to solve this is to let x be the initial price. Then, the new price is 1.06x, so $1.06x = 318$, which gives $x = 300$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69608 (x : ℝ) (h₁ : 1.06 * x = 318) : x = 300   :=  by sorry
