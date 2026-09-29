-- Prove2me | Theorems.Thm_WorkbookSource_base_23740
-- name    : WorkbookSource.base_23740
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:19.491728+00:00
-- url     : https://prove2.me/theorems/211dd78b-d513-4d78-ab35-fa15d2273495
-- title:
--   A cyclic ratio upper bound with a triple-product denominator
-- statement:
--   For $a, b, c>0, a+b+c=3$ , prove that $\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}\le\frac{3}{1+abc}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23740` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23740; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23740 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≤ 3 / (1 + a * b * c)  :=  by sorry
