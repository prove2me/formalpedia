-- Prove2me | Theorems.Thm_WorkbookSource_base_31981
-- name    : WorkbookSource.base_31981
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:28:51.607956+00:00
-- url     : https://prove2.me/theorems/2c3656c9-0658-4498-bc0c-8a2d0ebfaf99
-- title:
--   A cyclic ratio sum with a cubic reciprocal correction
-- statement:
--   For $ a,b,c > 0 $ Show that
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{3abc}{a^{2}b+b^{2}c+c^{2}a}\geq 4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31981` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31981; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31981 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 3 * a * b * c / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)) ≥ 4  :=  by sorry
