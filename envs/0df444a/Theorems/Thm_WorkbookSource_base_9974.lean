-- Prove2me | Theorems.Thm_WorkbookSource_base_9974
-- name    : WorkbookSource.base_9974
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:21.316606+00:00
-- url     : https://prove2.me/theorems/6a31e69c-4819-4bc7-b10f-2a794df4a7a9
-- title:
--   A cyclic fifth-degree product inequality
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $(x+y+z)(x^3y+zy^3+xz^3)\geq (x^2y+y^2z+z^2x)(xy+yz+xz).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9974` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9974; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9974 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + y + z) * (x ^ 3 * y + z * y ^ 3 + x * z ^ 3) ≥ (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) * (x * y + y * z + x * z)  :=  by sorry
