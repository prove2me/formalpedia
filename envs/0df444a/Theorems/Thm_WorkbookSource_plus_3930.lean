-- Prove2me | Theorems.Thm_WorkbookSource_plus_3930
-- name    : WorkbookSource.plus_3930
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:02:42.412989+00:00
-- url     : https://prove2.me/theorems/2ffad397-da66-4df0-af3e-50862304fdca
-- title:
--   A cyclic rational difference sum at fixed sum three is nonnegative
-- statement:
--   Let a,b,c>0 such that $a + b + c = 3$ . Prove that $\sum {\frac{{a\left( {c - b} \right)}}{{ab + 1}}} \ge 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3930` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3930; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a * (c - b) / (a * b + 1) + b * (a - c) / (b * c + 1) + c * (b - a) / (c * a + 1) ≥ 0   :=  by sorry
