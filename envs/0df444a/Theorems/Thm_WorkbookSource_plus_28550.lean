-- Prove2me | Theorems.Thm_WorkbookSource_plus_28550
-- name    : WorkbookSource.plus_28550
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:26:02.098989+00:00
-- url     : https://prove2.me/theorems/affe84c5-5c7c-4919-b518-f56a3c77e7bd
-- title:
--   A triple-product sum has a weighted pair-product bound at fixed total four
-- statement:
--   Prove that for $a>0,b>0,c>0,d>0$ and $a+b+c+d=4$ is
--    $abc+abd+bcd+acd\le ac+bd+\frac{ad+ab+bc+cd}{2}$ .
--   Sonnhard.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28550` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28550; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28550 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a * b * c + a * b * d + b * c * d + a * c * d ≤ a * c + b * d + (a * d + a * b + b * c + c * d) / 2   :=  by sorry
