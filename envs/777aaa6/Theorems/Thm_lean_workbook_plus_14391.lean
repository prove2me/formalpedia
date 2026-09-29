-- Prove2me | Theorems.Thm_lean_workbook_plus_14391
-- name    : lean_workbook_plus_14391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a41a6e74-1f64-429b-8ce9-d064e4da6770
-- statement:
--   By the triangle inequality: $|xy-1|=|(x-1)+(y-1)+(x-1)(y-1)|\leq |x-1|+|y-1|+|(x-1)(y-1)|$ \nSo $1+|xy-1|\leq 1+|x-1|+|y-1|+|x-1||y-1|=(1+|x-1|)(1+|y-1|)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14391  (x y : ℝ) :
  1 + |x * y - 1| ≤ (1 + |x - 1|) * (1 + |y - 1|)   :=  by sorry
