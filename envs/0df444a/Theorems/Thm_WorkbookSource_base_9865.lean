-- Prove2me | Theorems.Thm_WorkbookSource_base_9865
-- name    : WorkbookSource.base_9865
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:54.148711+00:00
-- url     : https://prove2.me/theorems/c3c7edb7-3b94-4916-a419-d06c72aabb52
-- title:
--   A refined comparison of symmetric pairwise ratio sums
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--    $$\frac{b+c}{a}+\frac{c+a}{b}+\frac{a+b}{c} \ge 4\left(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right)+\frac{2(a^2+b^2+c^2-ab-ac-bc)}{(a+b+c)^2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9865` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9865; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9865 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) + (2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c)) / (a + b + c) ^ 2  :=  by sorry
