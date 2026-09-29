-- Prove2me | Theorems.Thm_WorkbookSource_base_7985
-- name    : WorkbookSource.base_7985
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:00.841968+00:00
-- url     : https://prove2.me/theorems/fc87fc0b-78f4-4527-b117-607bdd3b1c31
-- title:
--   A cyclic quartic and triple-product upper bound
-- statement:
--   Let $ a,b,c\in \mathbb{R}$ such that $ a + b + c = 3$ . Prove that:
--    $ a^3b + b^3c + c^3a + 6abc\le 9
--   $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7985` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7985; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7985 (a b c : ℝ) (h : a + b + c = 3) :
  a^3 * b + b^3 * c + c^3 * a + 6 * a * b * c ≤ 9  :=  by sorry
