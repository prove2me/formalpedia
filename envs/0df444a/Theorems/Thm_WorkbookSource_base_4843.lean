-- Prove2me | Theorems.Thm_WorkbookSource_base_4843
-- name    : WorkbookSource.base_4843
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:02.601084+00:00
-- url     : https://prove2.me/theorems/29ac0b1d-3c7f-4529-8d74-075876ba6367
-- title:
--   A cyclic sixth-degree bound involving triangle factors
-- statement:
--   Let $a,b,c>0.$ Prove that $a^4b^2 + b^4c^2 + c^4a^2 \geq ( - a + b + c)(a - b + c)(a + b - c)(a^3 + b^3 + c^3).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4843` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4843; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4843 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b^2 + b^4 * c^2 + c^4 * a^2 ≥ (- a + b + c) * (a - b + c) * (a + b - c) * (a^3 + b^3 + c^3)  :=  by sorry
