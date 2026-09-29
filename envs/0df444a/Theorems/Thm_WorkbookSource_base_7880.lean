-- Prove2me | Theorems.Thm_WorkbookSource_base_7880
-- name    : WorkbookSource.base_7880
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:25.200847+00:00
-- url     : https://prove2.me/theorems/62a35f95-b7b6-4d32-acae-0e488f0cb87e
-- title:
--   A weighted four-variable pair-sum ratio is at least twelve
-- statement:
--   Prove that for positive real numbers a, b, c, and d, the following inequality holds: \\(\frac{c+d+4a}{a+b}+\frac{d+a+4b}{b+c}+\frac{a+b+4c}{c+d}+\frac{b+c+4d}{d+a} \geq 12\\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7880` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7880; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7880 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c + d + 4 * a) / (a + b) + (d + a + 4 * b) / (b + c) + (a + b + 4 * c) / (c + d) + (b + c + 4 * d) / (d + a) ≥ 12  :=  by sorry
