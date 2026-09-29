-- Prove2me | Theorems.Thm_WorkbookSource_base_9719
-- name    : WorkbookSource.base_9719
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:37:24.540466+00:00
-- url     : https://prove2.me/theorems/792d1806-7783-42e0-a26f-69187045e004
-- title:
--   A four-variable complementary product bound
-- statement:
--   Prove that if $x,y,z,t>0 ,x+y+z+t=1 $ then $(1-x)(1-y)(1-z)(1-t)\leq\frac{5}{16}+xyzt$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9719` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9719; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9719 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) (h : x + y + z + t = 1) : (1 - x) * (1 - y) * (1 - z) * (1 - t) ≤ 5 / 16 + x * y * z * t  :=  by sorry
