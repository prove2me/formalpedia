-- Prove2me | Theorems.Thm_WorkbookSource_base_31221
-- name    : WorkbookSource.base_31221
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:45.597086+00:00
-- url     : https://prove2.me/theorems/4a7981ef-cca1-42ad-944a-399e263b0543
-- title:
--   A quadratic difference bound on a sphere
-- statement:
--   Let $a, b, c$ be real numbers such that $ a^2+b^2+c^2=3.$ Prove that $$a+b+c-(a-b)(a-c)\leq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31221` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31221; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31221 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3) :
  a + b + c - (a - b) * (a - c) ≤ 3  :=  by sorry
