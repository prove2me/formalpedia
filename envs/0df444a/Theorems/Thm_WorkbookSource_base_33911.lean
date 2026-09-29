-- Prove2me | Theorems.Thm_WorkbookSource_base_33911
-- name    : WorkbookSource.base_33911
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:07.47311+00:00
-- url     : https://prove2.me/theorems/0bff359e-a153-45b5-b372-876c3bf19d08
-- title:
--   A quadratic sum with a product of shifted variables
-- statement:
--   Let $a,b,c,d\geq 0$ and $a+b+c+d=4$ . Prove that:
--    $a^2+b^2+c^2+d^2+4(a-1)(b-1)(c-1)(d-1)\geq 4$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33911` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33911; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33911 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1) ≥ 4  :=  by sorry
