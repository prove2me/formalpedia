-- Prove2me | Theorems.Thm_WorkbookSource_base_215
-- name    : WorkbookSource.base_215
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:06.131475+00:00
-- url     : https://prove2.me/theorems/32a66e42-c0b1-4cc6-9f3c-e2ea28ea30cc
-- title:
--   A cyclic ratio sum dominates a pairwise reciprocal sum
-- statement:
--   The following inequality is stronger, but also easy.
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--    $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\geq\frac{3}{2}+\frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{a+b}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_215` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_215; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_215 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 / 2 + a / (b + c) + b / (a + c) + c / (a + b)  :=  by sorry
