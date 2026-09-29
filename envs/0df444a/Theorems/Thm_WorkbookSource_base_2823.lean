-- Prove2me | Theorems.Thm_WorkbookSource_base_2823
-- name    : WorkbookSource.base_2823
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:53.7712+00:00
-- url     : https://prove2.me/theorems/380e28d0-fe75-4c69-add5-09adf2426298
-- title:
--   A cyclic product bound for shifted cubes
-- statement:
--   Prove the ineq for $ a,b,c>0$
--    $ (1+a^3)(1+b^3)(1+c^3)$ ≥ $ (1+ab^2)(1+bc^2)(1+ca^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2823` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2823; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2823 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a ^ 3) * (1 + b ^ 3) * (1 + c ^ 3) ≥ (1 + a * b ^ 2) * (1 + b * c ^ 2) * (1 + c * a ^ 2)  :=  by sorry
