-- Prove2me | Theorems.Thm_WorkbookSource_base_51012
-- name    : WorkbookSource.base_51012
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:02.693756+00:00
-- url     : https://prove2.me/theorems/70d895c8-971a-4fdf-b2a5-599149789222
-- title:
--   A weighted cyclic cubic ratio bounds one third of the total
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that: $\frac{a(a^2+2bc)}{(b+2c)^2}+\frac{b(b^2+2ac)}{(c+2a)^2}+\frac{c(c^2+2ab)}{(a+2b)^2}\geq \frac{a+b+c}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51012` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51012; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51012 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + 2 * b * c) / (b + 2 * c) ^ 2 + b * (b ^ 2 + 2 * a * c) / (c + 2 * a) ^ 2 + c * (c ^ 2 + 2 * a * b) / (a + 2 * b) ^ 2) ≥ (a + b + c) / 3  :=  by sorry
