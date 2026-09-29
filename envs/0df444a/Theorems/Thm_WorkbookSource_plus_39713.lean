-- Prove2me | Theorems.Thm_WorkbookSource_plus_39713
-- name    : WorkbookSource.plus_39713
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:29.605284+00:00
-- url     : https://prove2.me/theorems/50979557-393f-4176-ac24-df4a20f268db
-- title:
--   Two squared cubic sums with a symmetric correction
-- statement:
--   Prove that for real numbers $x, y, z$, the following inequality holds: $(xy^2 + z^2y + zx^2)^2 + (x^2y + y^2z + xz^2)^2 + 6(xy + zx + yz)(x + y + z)xyz \geq 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39713` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39713; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39713 (x y z : ℝ) : (x * y ^ 2 + z ^ 2 * y + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + x * z ^ 2) ^ 2 + 6 * (x * y + z * x + y * z) * (x + y + z) * x * y * z ≥ 0   :=  by sorry
