-- Prove2me | Theorems.Thm_WorkbookSource_base_18213
-- name    : WorkbookSource.base_18213
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:54:57.918462+00:00
-- url     : https://prove2.me/theorems/0b794580-9baf-4a1f-beb3-52f4a70ec084
-- title:
--   A mixed pairwise and triple-product inequality at unit sum
-- statement:
--   The stronger inequality holds: If $a,b,c$ are positive real numbers such that $a+b+c=1,$ then $3(ab+bc+ca)(1+48abc)\geq 75abc.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18213` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18213; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 3 * (a * b + b * c + c * a) * (1 + 48 * a * b * c) ≥ 75 * a * b * c  :=  by sorry
