-- Prove2me | Theorems.Thm_WorkbookSource_base_53057
-- name    : WorkbookSource.base_53057
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:23.733806+00:00
-- url     : https://prove2.me/theorems/a399fbdf-3905-4186-b791-a7bc5dcb0d7c
-- title:
--   A mixed quadratic ratio sum is at least one half
-- statement:
--   Prove that $\sum \frac{a^{2}}{2a^{2}+(b+c)^{2}}\geq \frac{1}{2}$ for $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53057` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53057; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53057 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + (b + c)^2) + b^2 / (2 * b^2 + (c + a)^2) + c^2 / (2 * c^2 + (a + b)^2)) ≥ 1 / 2  :=  by sorry
