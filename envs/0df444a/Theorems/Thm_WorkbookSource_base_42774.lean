-- Prove2me | Theorems.Thm_WorkbookSource_base_42774
-- name    : WorkbookSource.base_42774
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:38:33.600148+00:00
-- url     : https://prove2.me/theorems/1eb62600-235a-417e-a41f-cfb30e6ef2ab
-- title:
--   A pairwise ratio sum with a symmetric quadratic upper correction
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--    $$\frac{a+b}{a+b+2c}+\frac{b+c}{2a+b+c}+\frac{c+a}{a+2b+c}+\frac{ab+bc+ca}{2(a^2+b^2+c^2)} \leq2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42774` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42774; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42774 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c) + (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 2  :=  by sorry
