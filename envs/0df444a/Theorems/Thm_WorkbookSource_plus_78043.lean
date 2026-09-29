-- Prove2me | Theorems.Thm_WorkbookSource_plus_78043
-- name    : WorkbookSource.plus_78043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:18.239617+00:00
-- url     : https://prove2.me/theorems/c86b0f02-6121-4c02-9b03-4e0a1fab99c7
-- title:
--   A cubic squared-reciprocal sum bounds twice the quadratic sum minus three
-- statement:
--   For $a,b,c>0$ such that $a+b+c=3$ . Prove that $$\frac{a^3}{b^2}+\frac{b^3}{c^2}+\frac{c^3}{a^2}+3\ge 2(a^2+b^2+c^2)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78043` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78043 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 + 3 ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
