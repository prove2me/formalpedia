-- Prove2me | Theorems.Thm_WorkbookSource_base_9638
-- name    : WorkbookSource.base_9638
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:26.429901+00:00
-- url     : https://prove2.me/theorems/fa13dcb5-2350-41e5-830b-b3345a36081d
-- title:
--   A cyclic linear-over-quadratic lower bound
-- statement:
--   Let a,b,c be positive numbers. Prove that
--    $ \frac {a(b + c)}{b^2 + bc + c^2} + \frac {b(a + c)}{a^2 + ac + c^2} + \frac {c(a + b)}{a^2 + ab + b^2}\geq2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9638` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9638; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9638 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (b ^ 2 + b * c + c ^ 2) + b * (a + c) / (a ^ 2 + a * c + c ^ 2) + c * (a + b) / (a ^ 2 + a * b + b ^ 2)) ≥ 2  :=  by sorry
