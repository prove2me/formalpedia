-- Prove2me | Theorems.Thm_WorkbookSource_base_26618
-- name    : WorkbookSource.base_26618
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:27:33.185983+00:00
-- url     : https://prove2.me/theorems/0b71c1fe-891d-4fb0-9833-183259ac2c13
-- title:
--   A quartic and sextic cyclic product inequality
-- statement:
--   Let $x,y,z \in R$ ,prove that: $C.(x^4+y^4+z^4)(x^2y^4+y^2z^4+z^2x^4)\geq (xy^4+yz^4+zx^4)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26618` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26618; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26618 (x y z : ℝ) : (x^4 + y^4 + z^4) * (x^2 * y^4 + y^2 * z^4 + z^2 * x^4) ≥ (x * y^4 + y * z^4 + z * x^4)^2  :=  by sorry
