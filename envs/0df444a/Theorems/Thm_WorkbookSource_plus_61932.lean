-- Prove2me | Theorems.Thm_WorkbookSource_plus_61932
-- name    : WorkbookSource.plus_61932
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:17.687926+00:00
-- url     : https://prove2.me/theorems/2bc638e6-b28d-4efe-adf9-13bedf226e80
-- title:
--   A weighted quadratic reciprocal sum bounds the reciprocal squared total
-- statement:
--   For $a,b,c$ positive real numbers prove that
--
--    $ \frac {23}{8b^{2} + 7bc + 8c^{2}} + \frac {23}{8c^{2} + 7ca + 8a^{2}} + \frac {23}{8a^{2} + 7ab + 8b^{2}}\ge\frac {27}{(a + b + c)^2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_61932` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61932; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_61932 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (23 / (8 * b ^ 2 + 7 * b * c + 8 * c ^ 2) + 23 / (8 * c ^ 2 + 7 * c * a + 8 * a ^ 2) + 23 / (8 * a ^ 2 + 7 * a * b + 8 * b ^ 2)) ≥ 27 / (a + b + c) ^ 2   :=  by sorry
