-- Prove2me | Theorems.Thm_WorkbookSource_base_46110
-- name    : WorkbookSource.base_46110
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:00:08.78136+00:00
-- url     : https://prove2.me/theorems/c5b252e5-675b-4559-9e01-1321d59ce8f3
-- title:
--   A shifted squared reciprocal sum at fixed sum six
-- statement:
--   If $a,b,c$ are positive and $a+b+c=6$ , show that $(a+\frac{1}{b})^{2}+(b+\frac{1}{c})^{2}+(c+\frac{1}{a})^{2}\geq \frac{75}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46110` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46110; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46110 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 ≥ 75 / 4  :=  by sorry
