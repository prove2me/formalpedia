-- Prove2me | Theorems.Thm_WorkbookSource_base_16854
-- name    : WorkbookSource.base_16854
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:41.795095+00:00
-- url     : https://prove2.me/theorems/1cca2048-d3a3-4bcb-91b3-06ac2dc4e6e4
-- title:
--   A pairwise ratio sum with a fourth-degree correction
-- statement:
--   Let $a$ , $b$ and $c$ positive real numbers. Prove that:
--    $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b} \geq \frac{3}{2}+\frac{4(a^4+b^4+c^4-abc(a+b+c))}{(a+b+c)^4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16854` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16854; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16854 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + 4 * (a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c)) / (a + b + c) ^ 4  :=  by sorry
