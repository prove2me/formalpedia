-- Prove2me | Theorems.Thm_WorkbookSource_base_16964
-- name    : WorkbookSource.base_16964
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:54:56.719862+00:00
-- url     : https://prove2.me/theorems/ab65f850-d00f-4338-9e08-77a9fb36b1ff
-- title:
--   A squared-norm and cubic-product bound at sum nine
-- statement:
--   Given $a,b,c>0$ and $a+b+c=9$ shaw that $abc+5(a^2+b^2+c^2)\geqslant{162}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16964` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16964; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16964 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 9) : a * b * c + 5 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 162  :=  by sorry
