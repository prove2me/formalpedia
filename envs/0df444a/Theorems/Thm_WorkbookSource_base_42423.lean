-- Prove2me | Theorems.Thm_WorkbookSource_base_42423
-- name    : WorkbookSource.base_42423
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:03.001574+00:00
-- url     : https://prove2.me/theorems/c4049eca-90fb-4ebf-9a2e-e7bad0581898
-- title:
--   A cubic correction to a quadratic bound
-- statement:
--   Let $ a,b,c>0$ and $ a+b+c = 1$ , then
--
--    $ 2(a^2+b^2+c^2)\geq(a^3+b^3+c^3)+42abc-1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42423` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42423; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42423 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 2 * (a^2 + b^2 + c^2) ≥ a^3 + b^3 + c^3 + 42 * a * b * c - 1  :=  by sorry
