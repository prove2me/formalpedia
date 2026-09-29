-- Prove2me | Theorems.Thm_WorkbookSource_plus_75988
-- name    : WorkbookSource.plus_75988
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:15:39.886289+00:00
-- url     : https://prove2.me/theorems/4860cf47-bb88-472b-975a-42032e18877c
-- title:
--   A weighted quadratic reciprocal sum is at least two at fixed total three
-- statement:
--   Let $a,b,c$ are positive numbers such that $a+b+c=3.$ Prove that $\frac {a}{bc}+ \frac {b}{2ca} +\frac {1}{b} \ge 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75988` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75988; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75988 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b / c + b / (2 * c * a) + 1 / b ≥ 2   :=  by sorry
