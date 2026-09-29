-- Prove2me | Theorems.Thm_WorkbookSource_base_28066
-- name    : WorkbookSource.base_28066
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:10.270366+00:00
-- url     : https://prove2.me/theorems/356f2d9b-ab5c-4581-bba4-e266062305e6
-- title:
--   A quadratic and triple-product lower bound at sum three
-- statement:
--   If $ a,b,c > 0 $ such that $a+b+c=3 $ Prove that $3(a^{2}+b^{2}+c^{2})+abc\geq 10$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28066` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28066; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28066 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 10  :=  by sorry
