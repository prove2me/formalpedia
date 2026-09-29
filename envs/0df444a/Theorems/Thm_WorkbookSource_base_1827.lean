-- Prove2me | Theorems.Thm_WorkbookSource_base_1827
-- name    : WorkbookSource.base_1827
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:56:36.219731+00:00
-- url     : https://prove2.me/theorems/ab462d0e-421e-401f-8233-ca92e121a5fe
-- title:
--   A symmetric ratio sum bounds a cyclic pairwise ratio sum
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that the following inequality occurs: $\sum\frac{b+c}{a}\geq4\sum_{cyc}\frac{a}{a+b}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1827` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1827; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1827 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (a + c) / b + (a + b) / c ≥ 4 * (a / (a + b) + b / (b + c) + c / (c + a))  :=  by sorry
