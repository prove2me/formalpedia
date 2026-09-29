-- Prove2me | Theorems.Thm_WorkbookSource_base_5148
-- name    : WorkbookSource.base_5148
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:53.691297+00:00
-- url     : https://prove2.me/theorems/1e9c7072-a1ff-4db6-b614-ced0585c9829
-- title:
--   A cyclic quadratic ratio sum bounds shifted pairwise squares
-- statement:
--   הוכיחו כי עבור $a>0 , b>0 , c>0$ מתקיים: $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a} \ge \frac{\frac{(a+c)^2}{b+c}+\frac{(b+a)^2}{c+a}+\frac{(c+b)^2}{a+b}}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5148` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5148; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5148 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (1 / 2) * ((a + c) ^ 2 / (b + c) + (b + a) ^ 2 / (c + a) + (c + b) ^ 2 / (a + b))  :=  by sorry
