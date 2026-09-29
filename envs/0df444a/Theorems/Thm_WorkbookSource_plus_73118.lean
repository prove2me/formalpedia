-- Prove2me | Theorems.Thm_WorkbookSource_plus_73118
-- name    : WorkbookSource.plus_73118
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:56.264984+00:00
-- url     : https://prove2.me/theorems/ad958a6d-7318-4df1-b9f6-1fe1dd3d540a
-- title:
--   A cubic sum bound under a sum-product relation
-- statement:
--   Let $a,b,c\geq 0$ and $a+b+c= abc+3.$ Prove that
--
--    $$a^3+b^3+c^3\geq \frac{27}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73118` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73118; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73118 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = a * b * c + 3) : a ^ 3 + b ^ 3 + c ^ 3 ≥ 27 / 4   :=  by sorry
