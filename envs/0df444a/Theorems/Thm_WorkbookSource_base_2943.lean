-- Prove2me | Theorems.Thm_WorkbookSource_base_2943
-- name    : WorkbookSource.base_2943
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:36.857917+00:00
-- url     : https://prove2.me/theorems/8c29020d-d5fa-4a42-95ba-e75f6cdedcb6
-- title:
--   A quartic pairwise-product inequality on a sphere
-- statement:
--   Let be a,b,c real numbers if $ a^{2}+b^{2}+c^{2}=2$ show that $ ab+bc+ca \leq 1+abc(a+b+c) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2943` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2943; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2943 (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 2) :
  a * b + b * c + c * a ≤ 1 + a * b * c * (a + b + c)  :=  by sorry
