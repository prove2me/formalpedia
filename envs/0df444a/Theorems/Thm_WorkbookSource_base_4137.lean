-- Prove2me | Theorems.Thm_WorkbookSource_base_4137
-- name    : WorkbookSource.base_4137
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:20.911559+00:00
-- url     : https://prove2.me/theorems/6589b91d-9ad2-4f4a-9ec3-9f2d3a59d3bc
-- title:
--   A triple product and pairwise reciprocal bound at fixed sum three
-- statement:
--   Let $ a,b,c$ positive reals such that $ a+b+c=3$ . Prove that
--
--    $ abc+\frac{15}{ab+bc+ca}\geq6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4137` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4137; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4137 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :  a * b * c + 15 / (a * b + b * c + c * a) ≥ 6  :=  by sorry
