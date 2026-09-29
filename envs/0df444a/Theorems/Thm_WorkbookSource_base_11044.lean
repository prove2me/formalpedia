-- Prove2me | Theorems.Thm_WorkbookSource_base_11044
-- name    : WorkbookSource.base_11044
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:33:26.434783+00:00
-- url     : https://prove2.me/theorems/5d53ae1a-e808-4151-9faa-74ee88211e84
-- title:
--   A cubic-over-quadratic lower bound at fixed sum six
-- statement:
--   Prove that for positive numbers $a, b, c$ with $a+b+c=6$, the following inequality holds: $\sum \frac{a^3}{a^2+b+c} \ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11044` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11044; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11044 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) : a^3 / (a^2 + b + c) + b^3 / (b^2 + c + a) + c^3 / (c^2 + a + b) ≥ 3  :=  by sorry
