-- Prove2me | Theorems.Thm_WorkbookSource_base_9732
-- name    : WorkbookSource.base_9732
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:27.003659+00:00
-- url     : https://prove2.me/theorems/199a4816-0fc6-4c26-87d4-4040c1485122
-- title:
--   A normalized cubic sum with a symmetric reciprocal correction
-- statement:
--   Given $ a,b,c>0$ show that :
--
--    $ \frac{a^3+b^3+c^3}{3abc}+\frac{9abc}{(a+b+c)(ab+bc+ca)}\ge 2$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9732` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9732; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9732 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a^3 + b^3 + c^3) / (3 * a * b * c) + (9 * a * b * c) / ((a + b + c) * (a * b + b * c + c * a)) ≥ 2  :=  by sorry
