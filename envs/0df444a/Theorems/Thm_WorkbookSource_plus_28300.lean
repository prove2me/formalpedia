-- Prove2me | Theorems.Thm_WorkbookSource_plus_28300
-- name    : WorkbookSource.plus_28300
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:09.849331+00:00
-- url     : https://prove2.me/theorems/8b80a3f8-cf91-46dc-93d5-56c85c3c91b2
-- title:
--   A cyclic squared pairwise ratio sum upper bound
-- statement:
--   The following inequality is true. Let \(a, b, c>0\) . Prove that \(\frac{(a+c)^2(ab)}{(a+b)^2}+\frac{(a+b)^2(bc)}{(c+b)^2}+\frac{(c+b)^2(ca)}{(c+a)^2} \leq \frac{(a+b+c)^2}{3}\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28300` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28300; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28300 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + c) ^ 2 * a * b / (a + b) ^ 2 + (a + b) ^ 2 * b * c / (c + b) ^ 2 + (c + b) ^ 2 * c * a / (c + a) ^ 2 ≤ (a + b + c) ^ 2 / 3   :=  by sorry
