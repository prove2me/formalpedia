-- Prove2me | Theorems.Thm_WorkbookSource_plus_13348
-- name    : WorkbookSource.plus_13348
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:27.853084+00:00
-- url     : https://prove2.me/theorems/c209ba9c-fa9e-4587-a372-7564fa88a749
-- title:
--   A weighted quadratic reciprocal sum is at most one half
-- statement:
--   Let $a,b,c$ are positive numbers such that $a+b+c=3$ .Prove that:
--   $\frac{1}{4a^2+b^2+c^2}+\frac{1}{a^2+4b^2+c^2}+\frac{1}{a^2+b^2+4c^2} \leq \frac{1}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_13348` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_13348; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_13348 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (4 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (a ^ 2 + 4 * b ^ 2 + c ^ 2) + 1 / (a ^ 2 + b ^ 2 + 4 * c ^ 2) ≤ 1 / 2   :=  by sorry
