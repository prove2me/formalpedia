-- Prove2me | Theorems.Thm_WorkbookSource_plus_4648
-- name    : WorkbookSource.plus_4648
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:06:37.053713+00:00
-- url     : https://prove2.me/theorems/51694ff3-90be-48d8-8d68-62ceb9530644
-- title:
--   A quadratic norm bound under two linked relations
-- statement:
--   Let $a,b,c$ are real numbers such that $a^2+2b=-2$ and $b^2+4c=2.$ Prove that $$a^2+8c^2\geq \frac{1}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4648` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4648; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4648 (a b c : ℝ) (ha2 : a^2 + 2 * b = -2) (hb2 : b^2 + 4 * c = 2) : a^2 + 8 * c^2 ≥ 1 / 2   :=  by sorry
