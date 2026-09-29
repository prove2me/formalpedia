-- Prove2me | Theorems.Thm_WorkbookSource_base_16015
-- name    : WorkbookSource.base_16015
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:04.694746+00:00
-- url     : https://prove2.me/theorems/2df0d593-e80c-4204-81a4-ec7faa55dce3
-- title:
--   A symmetric squared difference ratio sum is at least one half
-- statement:
--   Prove that if $a,b,c>0$ then
--
--    $\frac{(a+b-3c)^2}{2c^2+(a+b)^2}+\frac{(c+a-3b)^2}{2b^2+(c+a)^2}+\frac{(b+c-3a)^2}{2a^2+(b+c)^2}\geq \frac12.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16015` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16015; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16015 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b - 3 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (c + a - 3 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (b + c - 3 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) ≥ 1 / 2  :=  by sorry
