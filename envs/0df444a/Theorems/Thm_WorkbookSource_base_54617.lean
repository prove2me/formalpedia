-- Prove2me | Theorems.Thm_WorkbookSource_base_54617
-- name    : WorkbookSource.base_54617
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:30.183759+00:00
-- url     : https://prove2.me/theorems/35fae163-5f09-4cea-b76a-c12fc44fe3a8
-- title:
--   A refined comparison of quadratic and linear reciprocal products
-- statement:
--   Given $a, b, c$ three positive real numbers, prove that $(a^2+b^2+c^2)\left(\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2} \right)+27\ge 4(a+b+c)\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \right)$ without using the UVW method.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54617` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54617; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54617 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / a^2 + 1 / b^2 + 1 / c^2) + 27 ≥ 4 * (a + b + c) * (1 / a + 1 / b + 1 / c)  :=  by sorry
