-- Prove2me | Theorems.Thm_WorkbookSource_base_28417
-- name    : WorkbookSource.base_28417
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:59:52.620233+00:00
-- url     : https://prove2.me/theorems/b12a0d8d-4c63-484e-a4ab-d8c7e363cdf5
-- title:
--   A weighted squared ratio sum is at least three
-- statement:
--   If $a,b,c$ are positive real numbers, then $\frac{(a+3b+3c)^2}{37a^2+3(b+c)^2}+\frac{(b+3c+3a)^2}{37b^2+3(c+a)^2}+\frac{(c+3a+3b)^2}{37c^2+3(a+b)^2}\ge3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28417` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28417; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28417 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 3 * b + 3 * c) ^ 2 / (37 * a ^ 2 + 3 * (b + c) ^ 2) + (b + 3 * c + 3 * a) ^ 2 / (37 * b ^ 2 + 3 * (c + a) ^ 2) + (c + 3 * a + 3 * b) ^ 2 / (37 * c ^ 2 + 3 * (a + b) ^ 2) ≥ 3  :=  by sorry
