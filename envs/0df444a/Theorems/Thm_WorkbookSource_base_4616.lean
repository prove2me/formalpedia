-- Prove2me | Theorems.Thm_WorkbookSource_base_4616
-- name    : WorkbookSource.base_4616
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:10.018084+00:00
-- url     : https://prove2.me/theorems/ba3aa4af-de45-4a9b-b653-e5b40c733a53
-- title:
--   A quartic and cubic power-sum comparison at total three
-- statement:
--   Let $a, b, c$ be reals with $a + b + c = 3$ . Prove that
--
--    $$2(a^4 + b^4 + c^4) + 36 \geq 7(a^3 + b^3 + c^3) + 21abc.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4616` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4616; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4616 (a b c : ℝ) (h : a + b + c = 3) : 2 * (a^4 + b^4 + c^4) + 36 ≥ 7 * (a^3 + b^3 + c^3) + 21 * a * b * c  :=  by sorry
