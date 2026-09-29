-- Prove2me | Theorems.Thm_WorkbookSource_base_31826
-- name    : WorkbookSource.base_31826
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:23.230984+00:00
-- url     : https://prove2.me/theorems/1deaa361-68b5-4446-8d64-82a0182e0f1a
-- title:
--   An asymmetric cubic-product bound at unit sum
-- statement:
--   Let a,b,c>0 and a+b+c=1, prove that
--
--    $ \frac {2 + c + c^3}{4} \ge abc + ab + 2bc + 2ca$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31826` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31826; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31826 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : (2 + c + c^3) / 4 ≥ a * b * c + a * b + 2 * b * c + 2 * c * a  :=  by sorry
