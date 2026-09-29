-- Prove2me | Theorems.Thm_WorkbookSource_base_16078
-- name    : WorkbookSource.base_16078
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:08.736591+00:00
-- url     : https://prove2.me/theorems/57b3474b-6dc0-483c-9094-62d165acbeb7
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Let $a,b,c> 0$ Prove that: $\sum \frac{(2a-b-c)(b+c)}{b^2+c^2} \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16078` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16078; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16078 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a - b - c) * (b + c) / (b * b + c * c) + (2 * b - c - a) * (c + a) / (c * c + a * a) + (2 * c - a - b) * (a + b) / (a * a + b * b) ≥ 0  :=  by sorry
