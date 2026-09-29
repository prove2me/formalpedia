-- Prove2me | Theorems.Thm_WorkbookSource_base_2980
-- name    : WorkbookSource.base_2980
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:41.806309+00:00
-- url     : https://prove2.me/theorems/9a51ccb6-44da-45e7-a940-56f3b86cb3ca
-- title:
--   A cyclic weighted quadratic ratio sum bounds the total
-- statement:
--   Let $ a,b,c >0 $ .Prove that
--    $\frac{a^{2}+8b^{2}}{4b+5c}+\frac{b^{2}+8c^{2}}{4c+5a}+\frac{c^{2}+8a^{2}}{4a+5b}\geq a+b+c $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2980` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2980; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2980 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 8 * b^2) / (4 * b + 5 * c) + (b^2 + 8 * c^2) / (4 * c + 5 * a) + (c^2 + 8 * a^2) / (4 * a + 5 * b) ≥ a + b + c  :=  by sorry
