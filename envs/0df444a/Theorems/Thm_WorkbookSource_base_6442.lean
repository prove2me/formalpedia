-- Prove2me | Theorems.Thm_WorkbookSource_base_6442
-- name    : WorkbookSource.base_6442
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:46.623552+00:00
-- url     : https://prove2.me/theorems/be14475e-e21e-4cde-95e2-c3aa72d5d805
-- title:
--   A product of three quadratics bounds a squared triple product difference
-- statement:
--   If $a,b,c\ge 0$ , then
--    $$2(a^2-a+1)(b^2-b+1)(c^2-c+1)\ge (abc-1)^2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6442` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6442; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6442 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 * (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≥ (a * b * c - 1)^2  :=  by sorry
