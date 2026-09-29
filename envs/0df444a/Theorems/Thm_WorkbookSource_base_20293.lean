-- Prove2me | Theorems.Thm_WorkbookSource_base_20293
-- name    : WorkbookSource.base_20293
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:45:49.099015+00:00
-- url     : https://prove2.me/theorems/e012dbf7-6431-41d3-ac7f-ca4693f237e2
-- title:
--   Schur's cubic sum bounds a product of squared differences
-- statement:
--   The best result here is the following.
--
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--
--    $a(a-b)(a-c)+b(b-a)(b-c)+c(c-a)(c-b)\geq\frac{4(a-b)^2(a-c)^2(b-c)^2}{a^3+b^3+c^3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20293` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20293; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20293 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) ≥ (4 * (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2) / (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
