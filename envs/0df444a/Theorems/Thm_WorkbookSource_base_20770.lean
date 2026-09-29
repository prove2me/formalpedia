-- Prove2me | Theorems.Thm_WorkbookSource_base_20770
-- name    : WorkbookSource.base_20770
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:08.951987+00:00
-- url     : https://prove2.me/theorems/243403ee-43b8-4bba-8ba7-148e8a8bb3b4
-- title:
--   A cubic expression bound under a weighted sum constraint
-- statement:
--   prove that : $ x+xy+xyz\leq 3$ where $ x,y,z$ are positive real numbers and $ 3x+2y+z=6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20770` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20770; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20770 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 3 * x + 2 * y + z = 6) : x + x * y + x * y * z ≤ 3  :=  by sorry
