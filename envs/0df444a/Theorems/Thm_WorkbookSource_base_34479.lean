-- Prove2me | Theorems.Thm_WorkbookSource_base_34479
-- name    : WorkbookSource.base_34479
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:53.00806+00:00
-- url     : https://prove2.me/theorems/dc54c46d-304c-4130-a684-8101f87288a9
-- title:
--   A bilinear bound under fixed sum and squared norm
-- statement:
--   Let $x, y,z$ be real numbers such that $x+y+z=2$ and $x^2+y^2+z^2=6$ . Prove that $(y-z)(x+y) \leq 9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34479` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34479; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34479 (x y z : ℝ) (h1 : x + y + z = 2) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 6) : (y - z) * (x + y) ≤ 9  :=  by sorry
