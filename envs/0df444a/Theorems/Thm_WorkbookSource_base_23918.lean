-- Prove2me | Theorems.Thm_WorkbookSource_base_23918
-- name    : WorkbookSource.base_23918
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:00:07.615149+00:00
-- url     : https://prove2.me/theorems/63ee6409-c688-4911-94fd-b197565d4618
-- title:
--   A cubic reciprocal upper bound at fixed sum two
-- statement:
--   Prove that $\sum_{cyc}\frac{1}{a^3 + a} \leq \frac{1}{abc}$ for $a + b + c = 2$, where $a, b, c$ are positive numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23918` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23918; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23918 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : (1 / (a ^ 3 + a) + 1 / (b ^ 3 + b) + 1 / (c ^ 3 + c)) ≤ 1 / (a * b * c)  :=  by sorry
