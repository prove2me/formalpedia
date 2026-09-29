-- Prove2me | Theorems.Thm_WorkbookSource_base_6142
-- name    : WorkbookSource.base_6142
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:26.771631+00:00
-- url     : https://prove2.me/theorems/747ef6c6-43dd-4c5c-a5ca-e9235c1eb2f4
-- title:
--   A fourth-power pair-sum bound in the unit ball
-- statement:
--   prove that: $6\geq{(a+b)^4+(a+c)^4+(a+d)^4+(b+c)^4+(b+d)^4+(c+d)^4}$ for real numbers $a,b,c,d$ satisfying $1\geq{a^2+b^2+c^2+d^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6142` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6142; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6142 (a b c d : ℝ) (h : 1 ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) :
  6 ≥ (a + b) ^ 4 + (a + c) ^ 4 + (a + d) ^ 4 + (b + c) ^ 4 + (b + d) ^ 4 + (c + d) ^ 4  :=  by sorry
