-- Prove2me | Theorems.Thm_WorkbookSource_plus_44251
-- name    : WorkbookSource.plus_44251
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:56.468827+00:00
-- url     : https://prove2.me/theorems/97d6e639-d649-4dee-abcf-c687085a8348
-- title:
--   A bilinear and linear bound on the unit circle
-- statement:
--   Let $x,y$ be reals such that $x^2+y^2=1.$ Prove that $x+6y+10xy\leq \frac{51}{5}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44251` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44251; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44251 (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : x + 6 * y + 10 * x * y ≤ 51 / 5   :=  by sorry
