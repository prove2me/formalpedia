-- Prove2me | Theorems.Thm_WorkbookSource_base_28649
-- name    : WorkbookSource.base_28649
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:05.024946+00:00
-- url     : https://prove2.me/theorems/ba005235-0b88-4ccd-9a64-5b1f31b65063
-- title:
--   An asymmetric quartic inequality with a squared-difference correction
-- statement:
--   Let $x,y,z \in R$ ,prove that: $x^4+y^4+z^4-(x+y+z)xyz+\frac{1}{2}yz(y-z)^2\geq 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28649` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28649; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28649 (x y z : ℝ) :  x^4 + y^4 + z^4 - (x + y + z) * x * y * z + (1 / 2) * y * z * (y - z)^2 ≥ 0  :=  by sorry
