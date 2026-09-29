-- Prove2me | Theorems.Thm_WorkbookSource_plus_69473
-- name    : WorkbookSource.plus_69473
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:12:09.290891+00:00
-- url     : https://prove2.me/theorems/3ca14fd7-4a1f-4c27-9eec-e6aa470d6d7f
-- title:
--   A product bound with positive unit sum
-- statement:
--   If $a+b+c=1$ where ( $a, b$ and $c$ are positive real numbers. Prove that $a^2+4bc\le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_69473` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_69473; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_69473 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) : a^2 + 4 * b * c ≤ 1   :=  by sorry
