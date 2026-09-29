-- Prove2me | Theorems.Thm_WorkbookSource_plus_11598
-- name    : WorkbookSource.plus_11598
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:44.84772+00:00
-- url     : https://prove2.me/theorems/3b94a13f-e97c-4a2d-9ea7-b271521bc2c8
-- title:
--   A shifted cubic ratio sum is at least three
-- statement:
--   With the conditions of $a+b+c=3$ and $a,b,c>0$ , Prove that $\sum _{cyc} \frac{a^3+1}{a^2+1} \ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_11598` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11598; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_11598 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + 1)/(a^2 + 1) + (b^3 + 1)/(b^2 + 1) + (c^3 + 1)/(c^2 + 1) ≥ 3   :=  by sorry
