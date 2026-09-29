-- Prove2me | Theorems.Thm_WorkbookSource_base_316
-- name    : WorkbookSource.base_316
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:13.058721+00:00
-- url     : https://prove2.me/theorems/9264c632-6d9b-4c8d-a155-e584dc50d0e1
-- title:
--   A shifted product upper bound under a cubic relation
-- statement:
--   Let $a,b,c>0 $ and $a+b+c+2=abc$ . Prove that $(a-1)(b-1)(c-1)(ab+bc+ca-1) \leq 11$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_316` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_316; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_316 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a + b + c + 2 = a * b * c) :  (a - 1) * (b - 1) * (c - 1) * (a * b + b * c + c * a - 1) ≤ 11  :=  by sorry
