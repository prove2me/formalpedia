-- Prove2me | Theorems.Thm_WorkbookSource_plus_62267
-- name    : WorkbookSource.plus_62267
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:49.139852+00:00
-- url     : https://prove2.me/theorems/d128a316-390d-4aef-942c-00b509fa16f1
-- title:
--   A quadratic form inequality
-- statement:
--   Prove that $2a^2+8b^2+5c^2\geq4ab+4ac+4bc$ given $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62267` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62267; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_62267 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2*a^2 + 8*b^2 + 5*c^2 ≥ 4*a*b + 4*a*c + 4*b*c   :=  by sorry
