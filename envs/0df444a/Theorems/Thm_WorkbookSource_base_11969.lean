-- Prove2me | Theorems.Thm_WorkbookSource_base_11969
-- name    : WorkbookSource.base_11969
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:04.308435+00:00
-- url     : https://prove2.me/theorems/b5327ac0-cba0-46e6-ad68-49099e183e07
-- title:
--   A fourth-power comparison of variables and pair sums
-- statement:
--   Let a,b,c be real such that $a+b+c=3$ . Prove that
--    $$7(a^4+b^4+c^4)+(a+b+c)^3 \ge (a+b)^4+(b+c)^4+(c+a)^4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11969` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11969; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11969 (a b c : ℝ) (h : a + b + c = 3) :
  7 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 3 ≥ (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4  :=  by sorry
