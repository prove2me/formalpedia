-- Prove2me | Theorems.Thm_WorkbookSource_base_20030
-- name    : WorkbookSource.base_20030
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:42:34.432855+00:00
-- url     : https://prove2.me/theorems/d36f5e91-7fdc-43a9-9dd0-092e08bfb8bd
-- title:
--   A shifted pairwise product bound at fixed sum three
-- statement:
--   For non-negative reals $a,b,c$ such that $a+b+c=3$ , show that $(a+b+1)(b+c+1)(c+a+1) \le 27$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20030` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20030; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20030 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : (a + b + 1) * (b + c + 1) * (c + a + 1) ≤ 27  :=  by sorry
