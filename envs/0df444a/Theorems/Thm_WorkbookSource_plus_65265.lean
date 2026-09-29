-- Prove2me | Theorems.Thm_WorkbookSource_plus_65265
-- name    : WorkbookSource.plus_65265
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:39.66084+00:00
-- url     : https://prove2.me/theorems/b0805ada-4f3a-4219-8ae7-a71e77fe2a67
-- title:
--   A squared reciprocal sum inequality at fixed sum three
-- statement:
--   For $a,b,c,>0$ such that $a+b+c=3$ Prove that $$3\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}-1\right)^2+1\ge \frac{4}{abc}+3\left(\frac{a}{bc}+\frac{b}{ca}+\frac{c}{ab}\right)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_65265` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_65265; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_65265 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 3 * (1 / a + 1 / b + 1 / c - 1) ^ 2 + 1 ≥ 4 / (a * b * c) + 3 * (a / (b * c) + b / (c * a) + c / (a * b))   :=  by sorry
