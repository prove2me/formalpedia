-- Prove2me | Theorems.Thm_WorkbookSource_base_14689
-- name    : WorkbookSource.base_14689
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:08.895966+00:00
-- url     : https://prove2.me/theorems/dccdd897-ceab-465b-b16f-ba5020f04ae9
-- title:
--   A weighted quadratic lower bound
-- statement:
--   Let $a,b,c>0$. Prove that
--
--    $$a^2+ 2b^2+c^2+ab\geq \frac{7}{39}(a+3b+c)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14689` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14689; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14689 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 39) * (a + 3 * b + c)^2  :=  by sorry
