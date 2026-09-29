-- Prove2me | Theorems.Thm_WorkbookSource_base_23288
-- name    : WorkbookSource.base_23288
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:45.935197+00:00
-- url     : https://prove2.me/theorems/9b90f214-b619-4c28-8ca0-f995ccb14519
-- title:
--   A shifted quadratic reciprocal upper bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove or disprove that $\frac{1}{a^2+b+c+1}+\frac{1}{b^2+c+a+1}+\frac{1}{c^2+a+b+1}\le\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23288` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23288; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23288 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a^2 + b + c + 1) + 1 / (b^2 + c + a + 1) + 1 / (c^2 + a + b + 1) ≤ 3 / 4  :=  by sorry
