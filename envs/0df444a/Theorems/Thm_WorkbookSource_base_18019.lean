-- Prove2me | Theorems.Thm_WorkbookSource_base_18019
-- name    : WorkbookSource.base_18019
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:39.01416+00:00
-- url     : https://prove2.me/theorems/c1edcbe8-0f48-4d9b-8009-189e35938e4b
-- title:
--   A cyclic weighted linear ratio upper bound
-- statement:
--   Let $a,b,c>0$ , prove that:
--    $$\frac a{3a+b}+\frac b{3b+c}+\frac c{3c+a}\le\frac34.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18019` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18019; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18019 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (3 * a + b) + b / (3 * b + c) + c / (3 * c + a)) ≤ 3 / 4  :=  by sorry
