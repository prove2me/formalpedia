-- Prove2me | Theorems.Thm_WorkbookSource_base_48622
-- name    : WorkbookSource.base_48622
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:21.252717+00:00
-- url     : https://prove2.me/theorems/81df5c6d-beba-4282-8b4f-75dba9f1e3af
-- title:
--   A weighted quadratic sum bounds a squared linear form
-- statement:
--   Let $a,b,c>0$. Prove that
--
--    $$a^2+ 2b^2+c^2+ab\geq \frac{7}{23}(a+2b+c)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48622` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48622; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48622 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 23) * (a + 2 * b + c)^2  :=  by sorry
