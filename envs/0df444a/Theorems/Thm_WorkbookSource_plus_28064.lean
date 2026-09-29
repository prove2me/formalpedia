-- Prove2me | Theorems.Thm_WorkbookSource_plus_28064
-- name    : WorkbookSource.plus_28064
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:49:39.840613+00:00
-- url     : https://prove2.me/theorems/02060217-5067-484a-80c9-f84c7b73816a
-- title:
--   A product of shifted squares with symmetric corrections
-- statement:
--   Prove that \((a^2+1)(b^2+1)(c^2+1)+(1+abc)(a^2+b^2+c^2)+abc\ge 15\) given \(a,b,c\ge 0\) and \(a+b+c=3\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28064` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28064; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28064 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + (1 + a * b * c) * (a^2 + b^2 + c^2) + a * b * c ≥ 15   :=  by sorry
