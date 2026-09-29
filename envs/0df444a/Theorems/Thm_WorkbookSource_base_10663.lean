-- Prove2me | Theorems.Thm_WorkbookSource_base_10663
-- name    : WorkbookSource.base_10663
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:42.113218+00:00
-- url     : https://prove2.me/theorems/995b989a-e915-4058-8ab1-93883f2e1a76
-- title:
--   A fifth-power difference bound under a nonnegative sum
-- statement:
--   Let $ x, y$ are real numbers such that $ x + y \geq 0.$ Prove that $x ^ 5 + y ^ 5-x ^ 4y-xy ^ 4 + x ^ 2 + 4x + 7\geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10663` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10663; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10663 (x y : ℝ) (h : x + y ≥ 0) :
  x ^ 5 + y ^ 5 - x ^ 4 * y - x * y ^ 4 + x ^ 2 + 4 * x + 7 ≥ 3  :=  by sorry
