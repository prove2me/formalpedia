-- Prove2me | Theorems.Thm_WorkbookSource_plus_25374
-- name    : WorkbookSource.plus_25374
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:27:14.462101+00:00
-- url     : https://prove2.me/theorems/6a0c53a1-c1d2-46dd-88f7-e954d5e0ebeb
-- title:
--   A product of mixed quadratic differences at fixed sum three
-- statement:
--   Let $a,b,c\ge0$ and $a+b+c=3.$ Prove that $(3a-bc)(3b-ac)(3c-ab)\le8.$ (O. Rudenko)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_25374` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_25374; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_25374 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (3 * a - b * c) * (3 * b - a * c) * (3 * c - a * b) ≤ 8   :=  by sorry
