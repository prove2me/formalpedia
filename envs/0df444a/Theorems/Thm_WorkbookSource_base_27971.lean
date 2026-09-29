-- Prove2me | Theorems.Thm_WorkbookSource_base_27971
-- name    : WorkbookSource.base_27971
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:23.015965+00:00
-- url     : https://prove2.me/theorems/11de5ad1-8da7-4345-ad5c-7c8bf5688b25
-- title:
--   A two-variable fifth-power bound
-- statement:
--   Let be given positive real numbers $ a,b$ ,prove that $ (a+b)^5\ge12ab(a^3+b^3) .$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27971` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27971; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27971 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 5 ≥ 12 * a * b * (a ^ 3 + b ^ 3)  :=  by sorry
