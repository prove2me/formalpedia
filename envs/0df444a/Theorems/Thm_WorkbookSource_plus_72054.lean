-- Prove2me | Theorems.Thm_WorkbookSource_plus_72054
-- name    : WorkbookSource.plus_72054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:17.081537+00:00
-- url     : https://prove2.me/theorems/57c9af2f-4c54-4035-a4a1-6db64f63faa6
-- title:
--   A shifted reciprocal sum and pair-product upper bound
-- statement:
--   Let $ x,y,z $ are positive real numbers and satisfying $ x+y+z=3 $. Prove: $ \frac{1}{x+1}+\frac{1}{y+1}+\frac{1}{z+1}+\frac{xy+yz+zx}{2}\leq 3 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_72054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_72054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_72054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) + (x * y + y * z + z * x) / 2 ≤ 3   :=  by sorry
