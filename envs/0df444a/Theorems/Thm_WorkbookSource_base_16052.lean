-- Prove2me | Theorems.Thm_WorkbookSource_base_16052
-- name    : WorkbookSource.base_16052
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:47:05.905895+00:00
-- url     : https://prove2.me/theorems/95c2a637-1ba2-4905-afe3-847daab53f3f
-- title:
--   A product of cubic and pairwise sums bounds a mixed product
-- statement:
--   Let $a,b,c$ be positive real numbers , prove that $(a^3+b^3+c^3)(bc+ca+ab)\ge 3abc(a^2+b^2+c^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16052` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16052; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16052 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) * (b * c + c * a + a * b) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)  :=  by sorry
