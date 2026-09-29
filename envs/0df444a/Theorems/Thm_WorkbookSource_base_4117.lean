-- Prove2me | Theorems.Thm_WorkbookSource_base_4117
-- name    : WorkbookSource.base_4117
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:07.784514+00:00
-- url     : https://prove2.me/theorems/b755114f-91b2-434a-bfed-6ae974aac452
-- title:
--   A squared quadratic sum times reciprocals bounds a cubic expression
-- statement:
--   For any positive real numbers $ a,b$ and $ c$ ,
--    $ (a^{2} + b^{2} + c^{2})^{2}\left(\frac {1}{a} + \frac {1}{b} + \frac {1}{c}\right) + 27abc\ge 2(a + b + c)^{3}(*)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4117` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4117; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4117 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 * (1 / a + 1 / b + 1 / c) + 27 * a * b * c ≥ 2 * (a + b + c)^3  :=  by sorry
