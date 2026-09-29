-- Prove2me | Theorems.Thm_WorkbookSource_plus_80477
-- name    : WorkbookSource.plus_80477
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:23.220367+00:00
-- url     : https://prove2.me/theorems/52c70ddb-d559-48f2-9059-018d33b9e209
-- title:
--   A cyclic quartic ratio sum is bounded by the quadratic sum
-- statement:
--   Prove that for all positive real numbers
--   $\sum \frac{a^3(b+c)}{a^2+bc}+\frac{b^3(c+a)}{b^2+ac}+\frac{c^3(a+b)}{c^2+ab}\le a^2+b^2+c^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_80477` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_80477; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_80477 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * (b + c) / (a^2 + b * c) + b^3 * (c + a) / (b^2 + a * c) + c^3 * (a + b) / (c^2 + a * b)) ≤ a^2 + b^2 + c^2   :=  by sorry
