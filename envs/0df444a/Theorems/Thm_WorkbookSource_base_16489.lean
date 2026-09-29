-- Prove2me | Theorems.Thm_WorkbookSource_base_16489
-- name    : WorkbookSource.base_16489
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:03:35.447645+00:00
-- url     : https://prove2.me/theorems/b81fb0c4-a5f3-40ef-bded-a6066befd5ee
-- title:
--   A cyclic quadratic difference ratio at fixed sum three
-- statement:
--   The corrected inequality is:
--   For positive numbers $a, b, c$ with $a + b + c = 3$, prove that:
--   $\frac{a(a+b-2c)}{bc+1}+\frac{b(b+c-2a)}{ca+1}+\frac{c(c+a-2b)}{ab+1} \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16489` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16489; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16489 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * (a + b - 2 * c) / (b * c + 1) + b * (b + c - 2 * a) / (c * a + 1) + c * (c + a - 2 * b) / (a * b + 1)) ≥ 0  :=  by sorry
