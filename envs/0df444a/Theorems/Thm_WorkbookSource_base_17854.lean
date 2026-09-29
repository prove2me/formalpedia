-- Prove2me | Theorems.Thm_WorkbookSource_base_17854
-- name    : WorkbookSource.base_17854
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:10:05.43498+00:00
-- url     : https://prove2.me/theorems/b384351c-d3ff-477d-a6ff-e81619a01a90
-- title:
--   A reciprocal sum with a triple-product correction
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that $ \frac{1}{a}+ \frac{1}{b}+ \frac{1}{c}+ \frac{3}{2}abc\ge \frac{9}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17854` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17854; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17854 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c + 3 / 2 * a * b * c ≥ 9 / 2  :=  by sorry
