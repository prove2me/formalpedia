-- Prove2me | Theorems.Thm_WorkbookSource_plus_16317
-- name    : WorkbookSource.plus_16317
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:12.41287+00:00
-- url     : https://prove2.me/theorems/8689e0d6-76b6-4025-9fb3-cb4cabc0227f
-- title:
--   A shifted cyclic quadratic ratio sum is at least three
-- statement:
--   Let $a, b, c$ be positive real numbers satisfying $a+b+c=3$ . Prove that: $\frac{{{a^2} + b}}{{{b^2} + a}} + \frac{{{b^2} + c}}{{{c^2} + b}} + \frac{{{c^2} + a}}{{{a^2} + c}} \ge 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_16317` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_16317; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_16317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b)/(b^2 + a) + (b^2 + c)/(c^2 + b) + (c^2 + a)/(a^2 + c) ≥ 3   :=  by sorry
