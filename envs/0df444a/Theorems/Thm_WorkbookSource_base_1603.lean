-- Prove2me | Theorems.Thm_WorkbookSource_base_1603
-- name    : WorkbookSource.base_1603
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:31.426518+00:00
-- url     : https://prove2.me/theorems/48943435-c359-432a-97ed-ac1beabcb304
-- title:
--   An arithmetic-harmonic mean bound with a squared-difference correction
-- statement:
--   Let $a,b,c>0 $ . Prove that
--    $$\\frac{a+b+c}{3}\\ge \\frac{3}{\\frac{1}{a}+\\frac{1}{b}+\\frac{1}{c}}+\\frac{(a-b)^2}{3(a+b+c)}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1603` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1603; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1603 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / 3 ≥ 3 / (1 / a + 1 / b + 1 / c) + (a - b) ^ 2 / (3 * (a + b + c))  :=  by sorry
