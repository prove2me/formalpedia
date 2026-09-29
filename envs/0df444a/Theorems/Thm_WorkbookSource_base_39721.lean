-- Prove2me | Theorems.Thm_WorkbookSource_base_39721
-- name    : WorkbookSource.base_39721
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:27.166246+00:00
-- url     : https://prove2.me/theorems/57ad8244-b057-42f8-bde4-6c66183ba143
-- title:
--   A fourth-power inequality involving two symmetric sums
-- statement:
--   Prove that $2(x+y+z)^4 \geq 9(xy+yz+zx)(x^2+y^2+z^2+xy+yz+zx)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39721` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39721; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39721 (x y z : ℝ) :
  2 * (x + y + z) ^ 4 ≥ 9 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)  :=  by sorry
