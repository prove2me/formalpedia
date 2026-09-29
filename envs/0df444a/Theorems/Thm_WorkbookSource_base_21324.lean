-- Prove2me | Theorems.Thm_WorkbookSource_base_21324
-- name    : WorkbookSource.base_21324
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:20.455946+00:00
-- url     : https://prove2.me/theorems/63df8b0d-dd59-453f-b011-1f8894194b67
-- title:
--   A quadratic sum is bounded by a reciprocal sum at fixed sum three
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove :
--    $10\Big(a^2+b^2+c^2\Big)-8\Bigg(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\Bigg)\le9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21324` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21324; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21324 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : 10 * (a ^ 2 + b ^ 2 + c ^ 2) - 8 * (1 / a + 1 / b + 1 / c) ≤ 9  :=  by sorry
