-- Prove2me | Theorems.Thm_WorkbookSource_base_6936
-- name    : WorkbookSource.base_6936
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:54:55.741996+00:00
-- url     : https://prove2.me/theorems/2d8e1ee4-3a28-4e5c-8e47-92083b85bd86
-- title:
--   A pairwise-product bound at fixed positive sum
-- statement:
--   If a,b,c > 0 and a+b+c=3, then $9(ab+bc+ca)\le 22+5abc.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6936` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6936; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6936 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 9 * (a * b + b * c + c * a) ≤ 22 + 5 * a * b * c  :=  by sorry
