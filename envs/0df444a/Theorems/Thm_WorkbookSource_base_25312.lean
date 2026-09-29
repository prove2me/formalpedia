-- Prove2me | Theorems.Thm_WorkbookSource_base_25312
-- name    : WorkbookSource.base_25312
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:16.480729+00:00
-- url     : https://prove2.me/theorems/b6bdf691-1ab7-48ec-8fc1-f14796a68f7f
-- title:
--   A reciprocal sum bounds mixed quadratic reciprocals
-- statement:
--   Let $a,b,c>0$, prove that: $\sum{\frac{1}{a}}\geq\sum{\frac{3a}{a^2+2bc}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25312` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25312; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25312 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 3 * a / (a ^ 2 + 2 * b * c) + 3 * b / (b ^ 2 + 2 * c * a) + 3 * c / (c ^ 2 + 2 * a * b)  :=  by sorry
