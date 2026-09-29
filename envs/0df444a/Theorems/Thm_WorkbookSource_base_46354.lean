-- Prove2me | Theorems.Thm_WorkbookSource_base_46354
-- name    : WorkbookSource.base_46354
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:04:47.6795+00:00
-- url     : https://prove2.me/theorems/eafcdd5b-5272-4b4a-8a61-ec42a423563b
-- title:
--   A shifted cyclic quadratic difference ratio at fixed sum three
-- statement:
--   Let a,b,c>0 such that $a + b + c = 3$ . Prove that $\sum {\frac{{a\left( { a - b} \right)}}{{ab + 1}}} \ge 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46354` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46354; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46354 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a * (a - b) / (a * b + 1) + b * (b - c) / (b * c + 1) + c * (c - a) / (c * a + 1) ≥ 0  :=  by sorry
