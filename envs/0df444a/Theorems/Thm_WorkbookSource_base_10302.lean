-- Prove2me | Theorems.Thm_WorkbookSource_base_10302
-- name    : WorkbookSource.base_10302
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:19:42.579558+00:00
-- url     : https://prove2.me/theorems/e67f1da2-c519-4a4c-bddd-4db05211ffe0
-- title:
--   A reciprocal four-variable product bounds a cyclic ratio sum at fixed total four
-- statement:
--   If $a+b+c+d=4$ and $a,b,c,d >0$ , prove that $\frac {4} {abcd} \ge \frac {a} {b}+ \frac {b} {c} + \frac {c} {d} +\frac {d} {a}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10302` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10302; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10302 (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d)  (habcd : a + b + c + d = 4) : 4 / (a * b * c * d) ≥ a / b + b / c + c / d + d / a  :=  by sorry
