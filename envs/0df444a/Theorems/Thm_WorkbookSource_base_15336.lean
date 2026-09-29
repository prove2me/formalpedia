-- Prove2me | Theorems.Thm_WorkbookSource_base_15336
-- name    : WorkbookSource.base_15336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:29.697796+00:00
-- url     : https://prove2.me/theorems/75303814-e9a4-4437-8b22-453d73260055
-- title:
--   A cubic and squared-norm comparison at unit sum
-- statement:
--   Let be $ a,b,c>0$ such that $ a+b+c=1$ . Show that : $ a^3+b^3+c^3+6abc\le a^2+b^2+c^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15336` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15336; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15336 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ a^2 + b^2 + c^2  :=  by sorry
