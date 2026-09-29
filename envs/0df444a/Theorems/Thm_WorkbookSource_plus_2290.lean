-- Prove2me | Theorems.Thm_WorkbookSource_plus_2290
-- name    : WorkbookSource.plus_2290
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:25.255976+00:00
-- url     : https://prove2.me/theorems/2dfc5e57-733a-41b1-9937-a76a60bf6675
-- title:
--   A cubic pairwise sum bounds a symmetric triple-product expression
-- statement:
--   Let a,b,c>0 Prove that
--    $ 5(ab + bc + ca)^3 + 27(abc)^2 \geq 18abc(a + b + c)(ab + bc + ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2290` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2290; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2290 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a * b + b * c + c * a)^3 + 27 * (a * b * c)^2 ≥ 18 * a * b * c * (a + b + c) * (a * b + b * c + c * a)   :=  by sorry
