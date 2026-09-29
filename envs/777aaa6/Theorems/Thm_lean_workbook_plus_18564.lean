-- Prove2me | Theorems.Thm_lean_workbook_plus_18564
-- name    : lean_workbook_plus_18564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ea97945a-db7a-4a61-bbe6-623f26e94329
-- statement:
--   For $ x,y,z\in\mathbb{R} ,x+y+z=4, $ show: $ |x-1|+\frac{|y|+|y-2|}{2}\ge 1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18564 (x y z : ℝ) (h : x + y + z = 4) : 1 ≤ |x - 1| + (|y| + |y - 2|) / 2   :=  by sorry
