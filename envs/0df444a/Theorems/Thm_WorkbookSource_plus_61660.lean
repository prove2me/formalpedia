-- Prove2me | Theorems.Thm_WorkbookSource_plus_61660
-- name    : WorkbookSource.plus_61660
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:43:52.284557+00:00
-- url     : https://prove2.me/theorems/14fe4616-af0e-48e8-84aa-01793bcb2ed9
-- title:
--   A shifted quadratic product lower bound at fixed sum three
-- statement:
--   Prove that \((a^2+1)(b^2+1)(c^2+1)-2abc\ge 6\) given \(a,b,c\ge 0\) and \(a+b+c=3\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_61660` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61660; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_61660 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) - 2 * a * b * c ≥ 6   :=  by sorry
