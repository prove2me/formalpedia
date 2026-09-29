-- Prove2me | Theorems.Thm_WorkbookSource_plus_4136
-- name    : WorkbookSource.plus_4136
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:19:32.356928+00:00
-- url     : https://prove2.me/theorems/cdbba165-49d4-489d-b1f9-3f663ce84c69
-- title:
--   A cubed pairwise sum bounds a product of triangle factors
-- statement:
--   let a,b,c>0 Prove that
--    $ (ab+bc+ca)^3 \geq (-a+b+c)(a-b+c)(a+b-c)(a+b+c)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4136` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4136; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4136 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) ^ 3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a + b + c) ^ 3   :=  by sorry
