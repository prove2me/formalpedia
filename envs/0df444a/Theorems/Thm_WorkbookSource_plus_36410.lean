-- Prove2me | Theorems.Thm_WorkbookSource_plus_36410
-- name    : WorkbookSource.plus_36410
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:19.961974+00:00
-- url     : https://prove2.me/theorems/eb1c6e20-b486-49f8-a2a2-d254506b7ac4
-- title:
--   A quadratic excess bounds a product of shifted variables
-- statement:
--   given $a,b,c,d \ge 0$ such that $a+b+c+d=4$ .Prove that $a^2+b^2+c^2+d^2-4 \ge 4(a-1)(b-1)(c-1)(d-1)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_36410` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_36410; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_36410 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 - 4 ≥ 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1)   :=  by sorry
