-- Prove2me | Theorems.Thm_WorkbookSource_base_3393
-- name    : WorkbookSource.base_3393
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:30.802984+00:00
-- url     : https://prove2.me/theorems/dd723c3c-a584-4c6c-a72f-b9973bb66aa7
-- title:
--   A fifth-power correction to a quadratic sum
-- statement:
--   Let $a,b\ge 0$ and $a+b=1.$ Prove that $a^2+b^2\le \frac{7}{16}+a^5+b^5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3393` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3393; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3393 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a^2 + b^2 ≤ 7 / 16 + a^5 + b^5  :=  by sorry
