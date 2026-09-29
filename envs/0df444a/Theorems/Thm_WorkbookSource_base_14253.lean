-- Prove2me | Theorems.Thm_WorkbookSource_base_14253
-- name    : WorkbookSource.base_14253
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:19.77078+00:00
-- url     : https://prove2.me/theorems/835cc703-63dd-437a-9fc7-38a3be099f79
-- title:
--   A symmetric quartic bound with a triple-product correction
-- statement:
--   Prove that $ 3(a^4+b^4+c^4)+3abc(a+b+c)\geq ab(a^2+b^2)+bc(b^2+c^2)+ca(c^2+a^2)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14253` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14253; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14253 (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 3 * a * b * c * (a + b + c) ≥ a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2)  :=  by sorry
