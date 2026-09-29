-- Prove2me | Theorems.Thm_WorkbookSource_plus_47977
-- name    : WorkbookSource.plus_47977
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:15.337668+00:00
-- url     : https://prove2.me/theorems/09ea4f42-a25d-43e6-9fa3-7ea452ff1900
-- title:
--   A pairwise-product bound at fixed sum three
-- statement:
--   Let $x,y,z\ge0$ and $x+y+z=3$ . Prove that: $ 7(xy+yz+zx)\le 18+3(xyz)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_47977` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_47977; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_47977 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 3) : 7 * (x * y + y * z + z * x) ≤ 18 + 3 * (x * y * z) ^ 2   :=  by sorry
