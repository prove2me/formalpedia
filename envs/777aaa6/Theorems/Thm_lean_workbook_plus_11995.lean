-- Prove2me | Theorems.Thm_lean_workbook_plus_11995
-- name    : lean_workbook_plus_11995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a101e5c3-6ddf-4bcc-8380-1a03d5340ab3
-- statement:
--   Let $a, b, c>0$ and $(a+b) (b+c) =4$ . Prove that $(2a+b) (a+b) +(b+2c) (b+c) \geq 8+ \frac{1}{2}(a+2b+c) (c+a) $ Determine when equality holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11995 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) = 4) :
  (2 * a + b) * (a + b) + (b + 2 * c) * (b + c) ≥ 8 + 1 / 2 * (a + 2 * b + c) * (c + a)   :=  by sorry
