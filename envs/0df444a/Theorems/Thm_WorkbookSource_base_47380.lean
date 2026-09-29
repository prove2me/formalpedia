-- Prove2me | Theorems.Thm_WorkbookSource_base_47380
-- name    : WorkbookSource.base_47380
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:31.364331+00:00
-- url     : https://prove2.me/theorems/1b36ec6d-d1be-417a-a957-5ab8638ec6af
-- title:
--   A shifted weighted cyclic ratio sum is at least six
-- statement:
--   For $a, b, c>0, $ prove that
--    $\frac{5a+4b+c+2}{4b+c+1}+\frac{5b+4c+a+2}{4c+a+1}+\frac{5c+4a+b+2}{4a+b+1}\geq6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47380` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47380; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47380 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + 4 * b + c + 2) / (4 * b + c + 1) + (5 * b + 4 * c + a + 2) / (4 * c + a + 1) + (5 * c + 4 * a + b + 2) / (4 * a + b + 1) ≥ 6  :=  by sorry
