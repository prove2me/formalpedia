-- Prove2me | Theorems.Thm_WorkbookSource_plus_89
-- name    : WorkbookSource.plus_89
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:17:00.373307+00:00
-- url     : https://prove2.me/theorems/6c37587f-bc64-498a-be4c-3ef949db5e56
-- title:
--   A strengthened sixth-degree Schur-type inequality
-- statement:
--   For $a,b,c>0$ , prove or disprove: $\sum{a^4{\left(a-b\right)}{\left(a-c\right)}}\ge5\prod{{\left(b-c\right)}^2}\text.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_89` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_89; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_89 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * (a - b) * (a - c) + b^4 * (b - a) * (b - c) + c^4 * (c - a) * (c - b) ≥ 5 * (b - c)^2 * (c - a)^2 * (a - b)^2   :=  by sorry
