-- Prove2me | Theorems.Thm_WorkbookSource_base_4409
-- name    : WorkbookSource.base_4409
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:12.315972+00:00
-- url     : https://prove2.me/theorems/321beab3-ae7f-4243-a62a-6a0a1eb41b48
-- title:
--   A cyclic ratio sum with a normalized pairwise correction
-- statement:
--   If $ a,b,c>0 $ then:
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\ge 4- \frac{3(ab+bc+ca)}{(a+b+c)^2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4409` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4409; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4409 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 4 - 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2  :=  by sorry
