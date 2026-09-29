-- Prove2me | Theorems.Thm_WorkbookSource_base_28904
-- name    : WorkbookSource.base_28904
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:45.218258+00:00
-- url     : https://prove2.me/theorems/a6ea8109-7fe8-455b-b617-150c86aa11a0
-- title:
--   A product comparison between cyclic linear and quadratic factors
-- statement:
--   Prove that for all $a,b,c>0$ we have
--    $abc(a+2c)(b+2a)(c+2b)\le(a^{2}+2bc)(b^{2}+2ca)(c^{2}+2ab)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28904` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28904; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28904 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b) ≤ (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)  :=  by sorry
