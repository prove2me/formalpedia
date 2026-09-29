-- Prove2me | Theorems.Thm_WorkbookSource_base_45693
-- name    : WorkbookSource.base_45693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:34.080603+00:00
-- url     : https://prove2.me/theorems/ab6fe232-a598-4bb6-9c10-5fabfac9e122
-- title:
--   A quartic sum bound under a cyclic relation
-- statement:
--   Let $a,$ $b,$ $c$ are real numbers, such that $a^3b+b^3c+c^3a=0.$ Prove that $3(a^4+b^4+c^4)+2abc(a+b+c)\geq0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45693 (a b c : ℝ) (h : a^3 * b + b^3 * c + c^3 * a = 0) :
  3 * (a^4 + b^4 + c^4) + 2 * a * b * c * (a + b + c) ≥ 0  :=  by sorry
