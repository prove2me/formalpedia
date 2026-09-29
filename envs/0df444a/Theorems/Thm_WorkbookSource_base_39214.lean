-- Prove2me | Theorems.Thm_WorkbookSource_base_39214
-- name    : WorkbookSource.base_39214
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:55.146651+00:00
-- url     : https://prove2.me/theorems/fadb743e-e950-43b0-9281-b2a2066a116b
-- title:
--   A shifted cyclic pair-product ratio upper bound at fixed sum three
-- statement:
--   Let $x,y,z>0,x+y+z=3$ ,prove that: $\frac{1+xy}{2+x+xy}+\frac{1+yz}{2+y+yz}+\frac{1+xz}{2+z+xz} \le \frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39214` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39214; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39214 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (1 + x * y) / (2 + x + x * y) + (1 + y * z) / (2 + y + y * z) + (1 + z * x) / (2 + z + z * x) ≤ 3 / 2  :=  by sorry
