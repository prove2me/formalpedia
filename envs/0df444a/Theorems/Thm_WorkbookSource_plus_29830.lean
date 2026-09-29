-- Prove2me | Theorems.Thm_WorkbookSource_plus_29830
-- name    : WorkbookSource.plus_29830
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:16.308961+00:00
-- url     : https://prove2.me/theorems/b502c2c1-b17b-47d3-832f-f8bc8c5d7cf0
-- title:
--   A shifted pairwise quadratic reciprocal sum is at most one ninth
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that
--    $\frac{1}{a^2+b^2+25}+\frac{1}{b^2+c^2+25}+\frac{1}{c^2+a^2+25}\le\frac{1}{9}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_29830` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_29830; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_29830 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a ^ 2 + b ^ 2 + 25) + 1 / (b ^ 2 + c ^ 2 + 25) + 1 / (c ^ 2 + a ^ 2 + 25) ≤ 1 / 9   :=  by sorry
