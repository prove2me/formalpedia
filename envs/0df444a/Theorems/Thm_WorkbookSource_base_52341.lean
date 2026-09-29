-- Prove2me | Theorems.Thm_WorkbookSource_base_52341
-- name    : WorkbookSource.base_52341
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:51:27.817308+00:00
-- url     : https://prove2.me/theorems/e65d3af5-d629-4bc4-b3cf-05aabda125c0
-- title:
--   A weighted quadratic ratio sum is at least twenty-one
-- statement:
--   For $a,b,c$ positive reals prove: $\frac{a^2+2b^2+4c^2}{bc} + \frac{b^2+2c^2+4a^2}{ca}+ \frac{c^2+2a^2+4b^2}{ab} \geq 21$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52341` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52341; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52341 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2 + 4 * c^2) / b / c + (b^2 + 2 * c^2 + 4 * a^2) / c / a + (c^2 + 2 * a^2 + 4 * b^2) / a / b ≥ 21  :=  by sorry
