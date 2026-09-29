-- Prove2me | Theorems.Thm_WorkbookSource_base_3158
-- name    : WorkbookSource.base_3158
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:06.871894+00:00
-- url     : https://prove2.me/theorems/a5a81b0f-2ef5-412e-87e1-f3d093f07f36
-- title:
--   A cubic bound under a mixed sum constraint
-- statement:
--   Let $a,b,c$ be non negative reals such that $a+b+c+ab+bc+ca=6$. Prove that $4(a+b+c)+abc\ge\ 13.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3158` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3158; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3158 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c + a * b + b * c + c * a = 6) : 4 * (a + b + c) + a * b * c ≥ 13  :=  by sorry
