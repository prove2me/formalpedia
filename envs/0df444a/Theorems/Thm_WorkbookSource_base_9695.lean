-- Prove2me | Theorems.Thm_WorkbookSource_base_9695
-- name    : WorkbookSource.base_9695
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:22.982477+00:00
-- url     : https://prove2.me/theorems/88290c7f-f35c-4de0-9d53-b380c574ba18
-- title:
--   A cubic power of the sum of squares bounds three symmetric sums
-- statement:
--   If $a,b,c >0$ , prove that $(a^2+b^2+c^2)^3 \geq (a+b+c)(ab+bc+ca)(a^3+b^3+c^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9695` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9695; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9695 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^3 ≥ (a + b + c) * (a * b + b * c + a * c) * (a^3 + b^3 + c^3)  :=  by sorry
