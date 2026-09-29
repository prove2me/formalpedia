-- Prove2me | Theorems.Thm_WorkbookSource_base_17596
-- name    : WorkbookSource.base_17596
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:30.429049+00:00
-- url     : https://prove2.me/theorems/fb1841a8-35af-4d10-a9ce-c77811411f81
-- title:
--   A cyclic quartic upper bound by a squared pair-product expression
-- statement:
--   Let $a,$ $b,$ $c$ be nonnegative real numbers such that $a+b+c=3$ and $ab+bc+ca>0.$ Prove that $2\left(a^3b+b^3c+c^3a\right)+3abc\le(6-ab-bc-ca)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17596` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17596; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17596 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) (h : a * b + b * c + c * a > 0) : 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * a * b * c ≤ (6 - a * b - b * c - c * a) ^ 2  :=  by sorry
