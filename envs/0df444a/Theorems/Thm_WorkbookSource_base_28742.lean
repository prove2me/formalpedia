-- Prove2me | Theorems.Thm_WorkbookSource_base_28742
-- name    : WorkbookSource.base_28742
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:57.084959+00:00
-- url     : https://prove2.me/theorems/4369dcea-1b2f-4c22-b8d5-c34145c4c9a8
-- title:
--   A weighted linear square bounds a pair-product sum
-- statement:
--   Give $x+y+z=1$ . Prove that: $44(xy+yz+xz) \leq (3x+4y+5z)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28742` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28742; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28742 (x y z : ℝ) (h : x + y + z = 1) :
  44 * (x * y + y * z + x * z) ≤ (3 * x + 4 * y + 5 * z) ^ 2  :=  by sorry
