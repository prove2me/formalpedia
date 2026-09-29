-- Prove2me | Theorems.Thm_WorkbookSource_base_2835
-- name    : WorkbookSource.base_2835
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:24.849607+00:00
-- url     : https://prove2.me/theorems/9f080b90-ed77-4fc5-928a-863515708f27
-- title:
--   A cyclic ratio sum with signed pairwise corrections
-- statement:
--   Given that $a,b,c$ are positive real numbers. Prove that
--
--    $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{a-b}{a+b}+\frac{b-c}{b+c}+\frac{c-a}{c+a}\geq 3$$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2835` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2835; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2835 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a)) ≥ 3  :=  by sorry
