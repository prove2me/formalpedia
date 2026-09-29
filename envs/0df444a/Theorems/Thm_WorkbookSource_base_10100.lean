-- Prove2me | Theorems.Thm_WorkbookSource_base_10100
-- name    : WorkbookSource.base_10100
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:26.180807+00:00
-- url     : https://prove2.me/theorems/716568b5-6a64-48b2-91c7-9d7abe6750a4
-- title:
--   A weighted pairwise quadratic sum has a squared lower bound
-- statement:
--   Let $a,b,c>0$ ,prove: $\frac{\left(3 (a+b)^2+2 (a+c)^2+(b+c)^2\right)^2}{a b c (a+b+c)}\geq 176$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10100` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10100; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10100 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a + b) ^ 2 + 2 * (a + c) ^ 2 + (b + c) ^ 2) ^ 2 / (a * b * c * (a + b + c)) ≥ 176  :=  by sorry
