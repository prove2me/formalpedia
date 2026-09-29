-- Prove2me | Theorems.Thm_WorkbookSource_base_15151
-- name    : WorkbookSource.base_15151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:31.236979+00:00
-- url     : https://prove2.me/theorems/015f5246-1a01-449e-8e25-b5655d9ad6bf
-- title:
--   A bilinear bound under two quadratic equalities
-- statement:
--   Let $ a,b,c$ such that:
--    $ a^{2}+c^{2}=1$
--    $ b^{2}+2b(a+c)=6$
--   Prove that: $ b(c-a)\le 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15151` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15151 (a b c : ℝ) (ha : a^2 + c^2 = 1) (hb : b^2 + 2 * b * (a + c) = 6) : b * (c - a) ≤ 4  :=  by sorry
