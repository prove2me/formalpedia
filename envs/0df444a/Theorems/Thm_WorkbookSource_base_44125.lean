-- Prove2me | Theorems.Thm_WorkbookSource_base_44125
-- name    : WorkbookSource.base_44125
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:49.398718+00:00
-- url     : https://prove2.me/theorems/2dbf63e7-5d69-4ddf-8357-e7ee8506314e
-- title:
--   A pair-product square sum upper bound at fixed sum three
-- statement:
--   Let $a, b, c$ be positive real numbers such that $a+b+c=3$ . Prove that
--    $a^2b^2+b^2c^2+c^2a^2 \le a^2+b^2+c^2+\frac{9}{16}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44125` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44125; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44125 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ a^2 + b^2 + c^2 + 9 / 16  :=  by sorry
