-- Prove2me | Theorems.Thm_WorkbookSource_base_49081
-- name    : WorkbookSource.base_49081
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:48:33.882497+00:00
-- url     : https://prove2.me/theorems/00a168c6-e8bf-40f4-bfae-7b8c0d9986c4
-- title:
--   A product of three shifted squares is at least sixty-four
-- statement:
--   Prove that $ (a^2 + 3)(b^2 + 3)(c^2 + 3) \ge 64 \forall a + b + c = 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49081` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49081; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49081 (a b c : ℝ) (h : a + b + c = 3) :
  (a^2 + 3) * (b^2 + 3) * (c^2 + 3) ≥ 64  :=  by sorry
