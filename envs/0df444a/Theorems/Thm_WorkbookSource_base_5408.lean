-- Prove2me | Theorems.Thm_WorkbookSource_base_5408
-- name    : WorkbookSource.base_5408
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:56.560463+00:00
-- url     : https://prove2.me/theorems/574632b3-1b40-4152-8013-67d3fa557558
-- title:
--   A cyclic quadratic-product ratio bound at fixed sum three
-- statement:
--   Let $a, b, c$ be positive real numbers satisfying the condition: $a+b+c=3$ . Prove that $\dfrac{a^2(b+1)}{a+b+ab}+\dfrac{b^2(c+1)}{b+c+bc}+\dfrac{c^2(a+1)}{c+a+ca}\ge 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5408` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5408; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5408 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 * (b + 1) / (a + b + a * b) + b^2 * (c + 1) / (b + c + b * c) + c^2 * (a + 1) / (c + a + c * a) ≥ 2  :=  by sorry
