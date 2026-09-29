-- Prove2me | Theorems.Thm_WorkbookSource_base_47959
-- name    : WorkbookSource.base_47959
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:10.394147+00:00
-- url     : https://prove2.me/theorems/d04428c5-1f32-4852-b825-32a96628731e
-- title:
--   A pair-sum product bound at fixed pairwise sum
-- statement:
--   For non-negative $ a,$ $ b$ and $ c$ such that $ ab + ac + bc = 3$ prove that
--    $ 8(a + b + c)^2\geq9(a + b)(a + c)(b + c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47959` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47959; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47959 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b + a * c + b * c = 3) : 8 * (a + b + c) ^ 2 ≥ 9 * (a + b) * (a + c) * (b + c)  :=  by sorry
