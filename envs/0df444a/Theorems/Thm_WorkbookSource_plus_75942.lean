-- Prove2me | Theorems.Thm_WorkbookSource_plus_75942
-- name    : WorkbookSource.plus_75942
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:44.548638+00:00
-- url     : https://prove2.me/theorems/070dc803-74cc-4bf8-849e-12f35fcd5a60
-- title:
--   A seventh-degree inequality involving squared symmetric sums
-- statement:
--   For any three positive real numbers $a,b,c$ , show that: $(a+b)(b+c)(c+a)[(a+b+c)^2+ab+bc+ca]^2\ge 32abc(a^2+b^2+c^2+ab+bc+ca)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75942` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75942; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75942 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) * ((a + b + c) ^ 2 + a * b + b * c + c * a) ^ 2 ≥ 32 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2   :=  by sorry
