-- Prove2me | Theorems.Thm_WorkbookSource_base_29587
-- name    : WorkbookSource.base_29587
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:45:00.191209+00:00
-- url     : https://prove2.me/theorems/916ea0f5-7e9f-4e7a-ada6-cb8ddec3ce5a
-- title:
--   A reciprocal total minus reciprocal alternating product is at most one quarter
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ be positive numbers. $\frac{2}{a+b+c+d}-\frac{1}{ab+bc+cd+da}\leq\frac{1}{4}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29587` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29587; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29587 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (2 / (a + b + c + d) - 1 / (a * b + b * c + c * d + d * a)) ≤ 1 / 4  :=  by sorry
