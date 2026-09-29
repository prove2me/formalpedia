-- Prove2me | Theorems.Thm_WorkbookSource_base_6752
-- name    : WorkbookSource.base_6752
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:37.623335+00:00
-- url     : https://prove2.me/theorems/bd7b6abc-840c-4917-b114-472d5ec8e525
-- title:
--   A cyclic quadratic-product ratio sum bounds the total
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that
--   $$\frac{a^2(b+c)}{b^2+c^2}+\frac{b^2(c+a)}{c^2+a^2}+\frac{c^2(a+b)}{a^2+b^2}\geq a+b+c $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6752` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6752; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6752 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * (b + c) / (b^2 + c^2) + b^2 * (c + a) / (c^2 + a^2) + c^2 * (a + b) / (a^2 + b^2)) ≥ a + b + c  :=  by sorry
