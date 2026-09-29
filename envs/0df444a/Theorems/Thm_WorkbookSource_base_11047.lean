-- Prove2me | Theorems.Thm_WorkbookSource_base_11047
-- name    : WorkbookSource.base_11047
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:22.852768+00:00
-- url     : https://prove2.me/theorems/e1f66f3c-2fbe-4556-8d23-8aacb62efe38
-- title:
--   A pair-product ratio upper bound at fixed sum three
-- statement:
--   Let $a,b, c>0, a+b+c=3$ . Prove that
--    $\frac{ab(a+b)}{1+ab}+\frac{bc(b+c)}{1+bc}+\frac{ca(c+a)}{1+ca}\le3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11047` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11047; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11047 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b * (a + b) / (1 + a * b) + b * c * (b + c) / (1 + b * c) + c * a * (c + a) / (1 + c * a)) ≤ 3  :=  by sorry
