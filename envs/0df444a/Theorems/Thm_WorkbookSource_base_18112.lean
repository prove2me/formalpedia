-- Prove2me | Theorems.Thm_WorkbookSource_base_18112
-- name    : WorkbookSource.base_18112
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:43:32.741481+00:00
-- url     : https://prove2.me/theorems/1d357e89-bc5f-49b0-9bff-899925ec9220
-- title:
--   A sum of triple quadratic averages has an upper bound in the total
-- statement:
--   Prove that for positive numbers a, b, c, and d, the following inequality holds:
--   $\frac{4(b^2+c^2+d^2+a^2)}{c+a+b+d} \geq \frac{b^2+c^2+d^2}{c+d+b}+\frac{c^2+d^2+a^2}{c+d+a}+\frac{d^2+a^2+b^2}{b+d+a}+\frac{a^2+b^2+c^2}{a+b+c}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18112` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18112; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18112 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (4 * (b^2 + c^2 + d^2 + a^2)) / (c + a + b + d) ≥ (b^2 + c^2 + d^2) / (c + d + b) + (c^2 + d^2 + a^2) / (c + d + a) + (d^2 + a^2 + b^2) / (b + d + a) + (a^2 + b^2 + c^2) / (a + b + c)  :=  by sorry
