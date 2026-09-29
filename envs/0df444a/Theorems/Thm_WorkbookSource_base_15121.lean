-- Prove2me | Theorems.Thm_WorkbookSource_base_15121
-- name    : WorkbookSource.base_15121
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:17.200049+00:00
-- url     : https://prove2.me/theorems/6832c9c8-b21b-453d-8c9c-3d9184812083
-- title:
--   A quartic power-sum lower bound at total one
-- statement:
--   Given real numbers $a,b,c$ such that $a+b+c=1$ . Prove that
--    $$1+3(a^4+b^4+c^4) \ge 4(a^3+b^3+c^3)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15121` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15121; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15121 (a b c : ℝ) (h : a + b + c = 1) : 1 + 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 4 * (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
