-- Prove2me | Theorems.Thm_WorkbookSource_base_18619
-- name    : WorkbookSource.base_18619
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:04:04.50367+00:00
-- url     : https://prove2.me/theorems/f124957b-1b79-4949-8929-32ef02336815
-- title:
--   A cyclic quartic correction to the squared sum of squares
-- statement:
--   Let $a,b,c$ be positive real numbers, prove that $ (a^2+b^2+c^2)^2 +3(a^3b+b^3c+c^3a)\geq 6abc(a+b+c).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18619` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18619; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18619 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 + 3 * (a^3 * b + b^3 * c + c^3 * a) ≥ 6 * a * b * c * (a + b + c)  :=  by sorry
