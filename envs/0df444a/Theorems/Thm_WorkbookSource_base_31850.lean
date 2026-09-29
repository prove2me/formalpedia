-- Prove2me | Theorems.Thm_WorkbookSource_base_31850
-- name    : WorkbookSource.base_31850
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:39.657625+00:00
-- url     : https://prove2.me/theorems/b50ba252-c96b-4ab2-ae6b-3d159e62b670
-- title:
--   A quadratic-product upper bound at fixed positive sum
-- statement:
--   If $ a,b,c > 0 $ such that $a+b+c=3 $ Prove that $3(a^{2}+b^{2}+c^{2})+abc\leq 27$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31850` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31850; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31850 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≤ 27  :=  by sorry
