-- Prove2me | Theorems.Thm_WorkbookSource_plus_49725
-- name    : WorkbookSource.plus_49725
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:41:06.967668+00:00
-- url     : https://prove2.me/theorems/cb30f416-998c-424d-90ef-fe82516d3b5e
-- title:
--   A linear and bilinear bound at fixed squared norm six
-- statement:
--   Let $a,b,c$ be real numbers such that $a^2+b^2+c^2=6$ . Prove that $2a+6b+6c-4bc-3ca\le 19.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_49725` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_49725; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_49725 (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 6) :
  2 * a + 6 * b + 6 * c - 4 * b * c - 3 * c * a ≤ 19   :=  by sorry
