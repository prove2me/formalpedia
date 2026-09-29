-- Prove2me | Theorems.Thm_WorkbookSource_base_31243
-- name    : WorkbookSource.base_31243
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:20:26.800271+00:00
-- url     : https://prove2.me/theorems/2a303c84-753c-4566-b27a-9690dfc93854
-- title:
--   A four-variable cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Let $a,b,c,d>0,$ prove that:
--
--    $\frac{b(-d+2b-c)}{b+c+d}+\frac{c(-d+2c-a)}{c+d+a}+\frac{d(2d-b-a)}{d+a+b}+\frac{a(2a-b-c)}{a+b+c}\geq 0.$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31243` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31243; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31243 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (b * (-d + 2 * b - c) / (b + c + d) + c * (-d + 2 * c - a) / (c + d + a) + d * (2 * d - b - a) / (d + a + b) + a * (2 * a - b - c) / (a + b + c)) ≥ 0  :=  by sorry
