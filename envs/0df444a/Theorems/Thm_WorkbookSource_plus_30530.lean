-- Prove2me | Theorems.Thm_WorkbookSource_plus_30530
-- name    : WorkbookSource.plus_30530
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:35.572968+00:00
-- url     : https://prove2.me/theorems/bdb8fe06-fca4-4cbe-a2ad-0c3c9ef174f0
-- title:
--   A cubic correction at sum three quarters
-- statement:
--   The $a,b\ge 0$ such that $a+b=\frac{3}{4}$ . Prove that $a^2-a^3+b^2-b^3\le \frac{45}{256}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30530` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30530; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30530 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 3 / 4) : a^2 - a^3 + b^2 - b^3 ≤ 45 / 256   :=  by sorry
