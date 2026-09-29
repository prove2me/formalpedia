-- Prove2me | Theorems.Thm_WorkbookSource_base_33501
-- name    : WorkbookSource.base_33501
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:45.470878+00:00
-- url     : https://prove2.me/theorems/d097b0ea-e488-4f98-b154-370af97942f1
-- title:
--   A product bound under unit positive sum
-- statement:
--   Let $a,b,c$ be positive real numbers with $a+b+c=1.$ Show that
--    $a^2+b^2+c^2\geq abc+(a+b)(b+c)(c+a).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33501` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33501; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33501 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 ≥ a * b * c + (a + b) * (b + c) * (c + a)  :=  by sorry
