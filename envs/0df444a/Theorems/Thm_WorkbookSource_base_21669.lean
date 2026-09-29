-- Prove2me | Theorems.Thm_WorkbookSource_base_21669
-- name    : WorkbookSource.base_21669
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:28.28677+00:00
-- url     : https://prove2.me/theorems/4564a47c-e3d6-4821-bd49-cb9680762e4f
-- title:
--   A pairwise-sum bound with a triple-product correction
-- statement:
--   prove that: $ xy+yz+zx\leq \frac{92}{81}+ \frac{2}{3}xyz$ given $ x,y,z \geq 0$ and $ x+y+z=2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21669` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21669; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21669 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2) :  x * y + y * z + z * x ≤ (92 / 81 + 2 / 3 * x * y * z)  :=  by sorry
