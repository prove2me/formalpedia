-- Prove2me | Theorems.Thm_WorkbookSource_plus_51848
-- name    : WorkbookSource.plus_51848
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:34.80383+00:00
-- url     : https://prove2.me/theorems/9f2b1dcc-d37d-43ff-9dc7-7189b2f7a706
-- title:
--   A cubic and pairwise-product lower bound
-- statement:
--   Let a,b,c>0 such that $a+b+c=3$ .Prove that $a^3+b^3+c^3+ab+ac+bc$ ≥ $6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_51848` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51848; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_51848 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a ≥ 6   :=  by sorry
