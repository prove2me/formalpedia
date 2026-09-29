-- Prove2me | Theorems.Thm_WorkbookSource_base_17035
-- name    : WorkbookSource.base_17035
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:06:15.408731+00:00
-- url     : https://prove2.me/theorems/48018159-0cc8-4e46-8c61-db31d0f3f407
-- title:
--   A pairwise ratio sum with a normalized triple-product correction
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that: $ \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+\frac{27abc}{2(a+b+c)^3}\ge 2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17035` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17035; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17035 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + (27 * a * b * c) / (2 * (a + b + c) ^ 3)) ≥ 2  :=  by sorry
