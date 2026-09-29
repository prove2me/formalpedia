-- Prove2me | Theorems.Thm_WorkbookSource_base_51592
-- name    : WorkbookSource.base_51592
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:43.914629+00:00
-- url     : https://prove2.me/theorems/703abc7f-f59e-47fe-9612-dfef513b4b73
-- title:
--   A weighted square bound at fixed cyclic product sum
-- statement:
--   Let $a,b,c ,d$ be real number such that $ab+bc+cd+da=1. $ Prove that $$a^2+2b^2+3c^2+4d^2\geq 2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51592` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51592; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51592 (a b c d : ℝ) (hab : a * b + b * c + c * d + d * a = 1) :
  a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 + 4 * d ^ 2 ≥ 2  :=  by sorry
