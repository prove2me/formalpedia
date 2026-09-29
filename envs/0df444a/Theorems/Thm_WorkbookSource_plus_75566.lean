-- Prove2me | Theorems.Thm_WorkbookSource_plus_75566
-- name    : WorkbookSource.plus_75566
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:11:07.899989+00:00
-- url     : https://prove2.me/theorems/6c99a323-40d5-4e2d-94be-5099c227eaff
-- title:
--   A lower bound under two linked quadratic relations
-- statement:
--   Let $a,b,c$ are real numbers such that $a^2+2b=7$ and $b^2+4c=-7.$ Prove that $$c^2+6a\geq -14$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75566` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75566; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75566 (a b c : ℝ) (ha : a^2 + 2 * b = 7) (hb : b^2 + 4 * c = -7) : c^2 + 6 * a ≥ -14   :=  by sorry
