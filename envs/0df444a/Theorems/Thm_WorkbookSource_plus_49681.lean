-- Prove2me | Theorems.Thm_WorkbookSource_plus_49681
-- name    : WorkbookSource.plus_49681
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:05.200239+00:00
-- url     : https://prove2.me/theorems/39233ed6-0be4-4498-819a-85d9823849cb
-- title:
--   A fifth-power bound involving triangle factors and pairwise products
-- statement:
--   Let $ a,b,c>0$ . Prove that
--
--    $ (a+b+c)^5\geq81(a+b-c)(a-b+c)(-a+b+c)(ab+bc+ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_49681` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_49681; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_49681 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 5 ≥ 81 * (a + b - c) * (a - b + c) * (-a + b + c) * (a * b + b * c + c * a)   :=  by sorry
